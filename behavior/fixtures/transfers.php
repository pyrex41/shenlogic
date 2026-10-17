<?php
// Domain API implementations are external contracts, recorded as assumptions.
function legacyTransfer($requestId, $amount) {
    require_authorized();
    debit($amount);
    credit($amount);
    publish_transfer($amount);
}
function intendedTransfer($requestId, $amount) {
    once($requestId, function() use ($amount) {
        require_authorized();
        debit($amount);
        credit($amount);
        publish_transfer($amount);
    });
}
function unresolvedTransfer($amount) {
    mysterious_mutation($amount);
}
