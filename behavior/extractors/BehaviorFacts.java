// Ghidra post-analysis script. Run via analyzeHeadless -postScript BehaviorFacts.java output.json
// @category ShenBehavior
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.*;
import ghidra.app.decompiler.*;
import com.google.gson.GsonBuilder;
import java.util.*;
import java.nio.file.*;
public class BehaviorFacts extends GhidraScript {
 private Map<String,List<List<Object>>> facts=new LinkedHashMap<>();
 private String artifact;
 private void add(String relation,Object... values){facts.computeIfAbsent(relation,k->new ArrayList<>()).add(Arrays.asList(values));}
 private String id(String kind,Object address){return artifact+":"+kind+":"+address;}
 public void run() throws Exception {
  String[] args=getScriptArgs();if(args.length!=1)throw new IllegalArgumentException("output.json required");
  artifact=currentProgram.getExecutableSHA256();
  if(artifact==null||artifact.isEmpty())throw new IllegalStateException("executable SHA256 unavailable; import an original file");
  for(String n:Arrays.asList("Node","Flow","Calls","DefUse","Reads","Writes","Boundary","Entry","Unknown","Contains"))facts.put(n,new ArrayList<>());
  List<Object> pcode=new ArrayList<>();
  DecompInterface decompiler=new DecompInterface();
  try {
   decompiler.openProgram(currentProgram);
   for(Function f:currentProgram.getFunctionManager().getFunctions(true)){
    monitor.checkCancelled();String fid=id("function",f.getEntryPoint());
    add("Node",fid,"function",currentProgram.getName(),0,0);add("Entry",f.getName(),fid);
    for(Instruction ins:currentProgram.getListing().getInstructions(f.getBody(),true)){
     String iid=id("instruction",ins.getAddress());add("Node",iid,ins.getMnemonicString(),currentProgram.getName(),0,0);add("Contains",fid,iid);
     if(ins.getFallThrough()!=null)add("Flow",iid,id("instruction",ins.getFallThrough()),"fallthrough");
     for(ghidra.program.model.address.Address target:ins.getFlows())if(!ins.getFlowType().isCall())add("Flow",iid,id("instruction",target),"branch");
     for(Reference ref:ins.getReferencesFrom())if(ref.getReferenceType().isCall()){
      Function target=currentProgram.getFunctionManager().getFunctionAt(ref.getToAddress());
      if(target!=null)add("Calls",iid,target.getName());else add("Unknown",iid,"unresolved-call:"+ref.getToAddress());
     }
     for(PcodeOp op:ins.getPcode()){
      if(op.getOpcode()==PcodeOp.CALLIND||op.getOpcode()==PcodeOp.BRANCHIND)add("Unknown",iid,"indirect-control-flow");
      if(op.getOpcode()==PcodeOp.LOAD)add("Reads",iid,"memory:unresolved");
      if(op.getOpcode()==PcodeOp.STORE)add("Writes",iid,"memory:unresolved");
     }
    }
    DecompileResults result=decompiler.decompileFunction(f,30,monitor);
    if(!result.decompileCompleted()){add("Unknown",fid,"decompilation-failed");continue;}
    Iterator<PcodeOpAST> ops=result.getHighFunction().getPcodeOps();
    while(ops.hasNext()){
     PcodeOpAST op=ops.next();String oid=id("pcode",op.getSeqnum());
     add("Node",oid,"pcode:"+op.getMnemonic(),currentProgram.getName(),0,0);add("Contains",fid,oid);
     Map<String,Object> record=new LinkedHashMap<>();record.put("id",oid);record.put("function",fid);record.put("opcode",op.getMnemonic());record.put("address",op.getSeqnum().getTarget().toString());
     List<String> inputs=new ArrayList<>();for(int j=0;j<op.getNumInputs();j++){Varnode v=op.getInput(j);inputs.add(v.toString());if(v.getDef()!=null)add("DefUse",id("pcode",v.getDef().getSeqnum()),oid,"ssa");}
     record.put("inputs",inputs);record.put("output",op.getOutput()==null?null:op.getOutput().toString());pcode.add(record);
    }
   }
  } finally {decompiler.dispose();}
  Map<String,Object> out=new LinkedHashMap<>();out.put("version",1);out.put("producer","ghidra");out.put("artifact",artifact);out.put("filename",currentProgram.getName());out.put("facts",facts);out.put("pcode",pcode);out.put("coverage",Map.of("cfg","partial","calls","partial","memory","unresolved-aliases","exceptions","not-recovered"));
  Files.writeString(Path.of(args[0]),new GsonBuilder().setPrettyPrinting().create().toJson(out));
 }
}
