-- A persistent data-only bridge. No request is evaluated as Shen source.
local root = assert(os.getenv('SHEN_LUA_ROOT'), 'SHEN_LUA_ROOT required')
package.path = root .. '/?.lua;' .. package.path
local shen = require('shen')
shen.boot{quiet=true, hush_load=true}
local R, P = shen.runtime, shen.prims
for _,file in ipairs({'shen/calculus.shen','shen/machine.shen'}) do
 local ok,e=pcall(shen.call,'load',file)
 if not ok then io.stderr:write(shen.call('error-to-string',e)..'\n');os.exit(1) end
end
local function decode(x)
  if R.is_cons(x) then
    local a = shen.totable(x)
    local tag = tostring(a[1])
    if tag == 's' then
      assert(type(a[2]) == 'string' and a[2]:match('^[0-9a-f]*$') and #a[2] % 2 == 0)
      return (a[2]:gsub('..', function(h) return string.char(tonumber(h,16)) end))
    elseif tag == 'l' then
      local out = {}; for i=2,#a do out[#out+1]=decode(a[i]) end
      return shen.list(out)
    end
    error('invalid wire tag')
  end
  assert(type(x)=='boolean' or (type(x)=='number' and x==math.floor(x) and math.abs(x)<=2147483647), 'invalid scalar')
  return x
end
local function quote(s)
  return '"' .. s:gsub('[%z\1-\31\\"]',function(c)
    if c=='"' then return '\\"' elseif c=='\\' then return '\\\\' end
    return string.format('\\u%04x',string.byte(c))
  end) .. '"'
end
local function json(x)
  if x == R.NIL then return '[]' end
  if R.is_cons(x) then
    local a=shen.totable(x); for i=1,#a do a[i]=json(a[i]) end
    return '['..table.concat(a,',')..']'
  end
  if type(x)=='string' then return quote(x) end
  if type(x)=='boolean' or type(x)=='number' then return tostring(x) end
  if R.is_symbol(x) then return quote(tostring(x)) end
  error('unsupported output')
end
-- Proof fields denoting contexts/effects are inert indices, not executable
-- expressions. Elaborate only proof constructors to Shen cons syntax.
local recursive={sequence={[5]=true,[6]=true},branches={[4]=true,[5]=true},
 invariant={[2]=true},transaction={[2]=true},deduplicate={[2]=true},
 ["by-affine-invariant"]={[2]=true},["by-durable-deduplication"]={[2]=true},["by-effect-inclusion"]={[3]=true}}
local function proofSyntax(p)
  local a=shen.totable(p);local positions=recursive[a[1]] or {};local tail=R.NIL
  for i=#a,1,-1 do
    local field=positions[i] and proofSyntax(a[i]) or a[i]
    tail=shen.list({R.intern('cons'),field,tail})
  end
  return tail
end
local function typecheck(proof, ty)
  P.GLOBALS['shen.*infs*']=0
  local ok, result = pcall(P.F['bt.check-ground'], proofSyntax(proof), ty)
  if not ok then io.stderr:write('typecheck: '..tostring(result)..'\n') end
  return ok and result ~= false
end
local logicLoaded=false
local function loadLogic()
 if logicLoaded then return end
 local f=assert(io.open('../shenlogic.shen','r'));local src=f:read('*a');f:close()
 for path in src:gmatch('%(load "([^"]+)"%)') do shen.call('load','../'..path) end
 src=src:gsub('%(load "[^"]+"%)','')
 shen.eval(src);logicLoaded=true
end
local function dispatch(a)
  local cmd = a[1]
  if cmd=='translate-source' then loadLogic();return shen.call('shenlogic.translate-file',a[2],a[3]) end
  if cmd=='infer' then return shen.call('bt.infer',a[2],a[3]) end
  if cmd=='check' then
    return typecheck(a[6],shen.list({R.intern('bt-proof'),a[2],a[3],a[4],a[5]}))
  end
  if cmd=='retry-safe' then
    return typecheck(a[5],shen.list({R.intern('bt-retry-safe'),a[2],a[3],a[4]}))
  end
  if cmd=='effects-within' then
    return typecheck(a[6],shen.list({R.intern('bt-effects-within'),a[2],a[3],a[4],a[5]}))
  end
  if cmd=='preserves' then
    return typecheck(a[7],shen.list({R.intern('bt-preserves'),a[2],a[3],a[4],a[5],a[6]}))
  end
  if cmd=='run' then return shen.call('bt.run',a[2],a[3],a[4],a[5]) end
  if cmd=='observe' then return shen.call('bt.observe',a[2],a[3],a[4],a[5],a[6]) end
  if cmd=='judge' then return shen.call('bt.judge',a[2],a[3],a[4],a[5]) end
  if cmd=='graph' then return shen.call('bt.graph',a[2]) end
  error('unknown command')
end
io.stdout:write('{"ready":true}\n');io.stdout:flush()
for line in io.lines() do
  local ok,result=pcall(function()
    assert(#line <= 4000000,'request too large')
    local forms=R.read_all(line);assert(#forms==1,'one request required')
    return dispatch(shen.totable(decode(forms[1])))
  end)
  if ok then
    local encoded,j=pcall(json,result)
    if encoded then io.stdout:write('{"ok":true,"value":'..j..'}\n')
    else io.stdout:write('{"ok":false,"error":'..quote(tostring(j))..'}\n') end
  else io.stdout:write('{"ok":false,"error":'..quote(tostring(result))..'}\n') end
  io.stdout:flush()
end
