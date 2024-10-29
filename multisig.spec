methods {

    function _.addValidator(address, uint256, uint256) external => DISPATCHER(true);
    function _.removeValidator(address, uint256, uint256) external => DISPATCHER(true);
    function _.replaceValidator(address, address) external => DISPATCHER(true);
    function _.changeQuorum(uint256, uint256) external => DISPATCHER(true);
    function distributeRewards() external;
    function isVoteToChangeValidator(bytes, address) external returns (bool) envfree;
    function getDataOfTransaction(bytes32) external returns (bytes memory) envfree;
    function WRAPPING_FEE() external returns(uint256) envfree;
    function rewardsPot() external returns(uint256) envfree;
    function sideRewardsPot() external returns(uint256) envfree;
    function usersValue() external returns(uint256) envfree;
    function lastWithdrawalTime() external returns(uint256) envfree;
    function isConfirmed(bytes32) external returns (bool) envfree;
    function hash(bytes) external returns (bytes32) envfree;
    function getConfirmationCount(bytes32) external returns (uint256) envfree;
    function transactionExists(bytes32) external returns (bool) envfree;
    function removeTransaction(bytes32) external;
    function executeTransaction(bytes32) external envfree;
    function _._ external => DISPATCH [
        currentContract.addValidator(address, uint256, uint256),
        currentContract.removeValidator(address, uint256, uint256),
        currentContract.replaceValidator(address, address),
        currentContract.changeQuorum(uint256, uint256),
        currentContract.removeTransaction(bytes32),
        currentContract.executeTransaction(bytes32)
    ] default NONDET;

}

persistent ghost mapping(mathint => mathint) fib
{
    axiom fib[0] == 1;
    axiom fib[1] == 1;
    axiom fib[2] == 2;
    axiom fib[3] == 3;
    axiom fib[4] == 5;
    axiom fib[5] == 8;
    axiom fib[6] == 13;
    axiom fib[7] == 21;
    axiom forall uint256 i. i < 20 => ((i != 0 && i != 1) => fib[i] == fib[i - 1] + fib[i - 2]);
    //axiom forall uint256 i. forall uint256 j. forall uint256 k. (i < j && j < k) => fib[i] + fib[j] <= fib[k];
}

function allInvariants(env e)
{
    requireInvariant uniqenessValidators(e);
    requireInvariant validatorNotZero(e);
    requireInvariant zeroNotValidator(e);
    requireInvariant validatorIsValid(e);
    requireInvariant zeroIsInValidatorsZero(e);
    requireInvariant uniqenessTransactionIds(e);
    requireInvariant transactionIdIsValid(e);
    requireInvariant quorumIsValid(e);
    requireInvariant zeroInTransactionIdsLength(e);
    requireInvariant validatorsSetToZero(e);
    requireInvariant transactionIdsReverseMapValid(e);
    requireInvariant zeroNotInTransactionIds(e);
    requireInvariant zeroInTransactionIdsZero(e);
    requireInvariant transactionIdsReverseMapZeroIsZero(e);
    requireInvariant lengthIsNotZero(e);
    requireInvariant validatorsReverseMapValid(e);
    requireInvariant validatorsReverseMapUniqeness(e);
    requireInvariant validatorsReverseMapReverse(e);
    requireInvariant validatorsReverseMapValidValue(e);
    requireInvariant canPayRewardsPot(e);
    requireInvariant validatorNotThis(e);
    requireInvariant thisNotValidator(e);
    requireInvariant reverseMapNotZero_IFF_IsValidator(e);
    // you can add invariants here///////////////////




////////////////////////////////////////////
    require e.block.timestamp != 0;
    require currentContract.transactionIds.length != 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
}

// addValidator succeeds only when the contract calls itself
rule addValidatorCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    addValidator(e, args);
    assert e.msg.sender == currentContract;
}

// length INCREASES only if the call is to addValidator, executeTransaction, or voteForTransaction
rule lengthChangeOnlyInAddValidatorActivation(method f)
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    uint256 lengthBefore = currentContract.validators.length;
    f(e, args);
    assert lengthBefore < currentContract.validators.length => f.selector == sig:addValidator(address, uint256, uint256).selector|| f.selector == sig:executeTransaction(bytes32).selector || f.selector == sig:voteForTransaction(bytes32, address, uint256, bytes, bool).selector;
}

// it's possible to increase the length using addValidator
rule lengthChangeWorks1()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    uint256 lengthBefore = currentContract.validators.length;
    addValidator(e, args);
    satisfy lengthBefore < currentContract.validators.length;
}

// it's possible to increase the length using executeTransaction
rule lengthChangeWorks2()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    uint256 lengthBefore = currentContract.validators.length;
    executeTransaction(e, args);
    satisfy lengthBefore < currentContract.validators.length;
}

// it's possible to increase the length using voteForTransaction
rule lengthChangeWorks3()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    uint256 lengthBefore = currentContract.validators.length;
    voteForTransaction(e, args);
    satisfy lengthBefore < currentContract.validators.length;
}

// if addValidator succeeds, it adds 1 validator
// addValidator doesn't change the validator
// the last validator is the added validator
rule addValidatorFunctinality()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    address a;
    uint256 lengthBefore = currentContract.validators.length;
    bool isAValidatorBefore = currentContract.isValidator[a];
    addValidator(e, args);
    assert lengthBefore == currentContract.validators.length - 1;
    assert isAValidatorBefore => currentContract.isValidator[a];
    assert !isAValidatorBefore && currentContract.isValidator[a] => currentContract.validators[assert_uint256(currentContract.validators.length - 1)] == a;
}

// it's possible to add some validator using addValidator
rule addValidatorFunctinality2()
{
    env e;
    allInvariants(e);
    
    address a;
    calldataarg args;
    bool isValidatorBefore = currentContract.isValidator[a];
    addValidator(e, args);

    satisfy !isValidatorBefore && currentContract.isValidator[a];
}

// When addValidator succeeds, the quorum and step are properly set and the added validator is a validator
rule addValidatorFunctinality3()
{
    env e;
    allInvariants(e);
    
    address a;
    uint256 newQuorum;
    uint256 step;
    addValidator(e, a, newQuorum, step);

    assert currentContract.isValidator[a] && currentContract.quorum == newQuorum && currentContract.step == step;
}

// adding a validator doesn't change the confirmation count
rule addValidatorFunctinality4()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    address a;
    bytes32 transactionId;
    bool isAValidatorBefore = currentContract.isValidator[a];
    uint256 count = getConfirmationCount(transactionId);
    addValidator(e, args);
    require !isAValidatorBefore && currentContract.isValidator[a];
    assert count == getConfirmationCount(transactionId);
}

// removing the validator can only be done by the current contract
rule removeValidatorCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    removeValidator(e, args);
    assert e.msg.sender == currentContract;
}

// inexact
// removeValidator removes one and only one validator
rule removeValidatorFunctinality()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    address a;
    address b;
    uint256 lengthBefore = currentContract.validators.length;
    bool isAValidatorBefore = currentContract.isValidator[a];
    bool isBValidatorBefore = currentContract.isValidator[b];
    removeValidator(e, args);
    assert lengthBefore == currentContract.validators.length + 1;
    assert !isAValidatorBefore => !currentContract.isValidator[a];
    assert (isAValidatorBefore && !currentContract.isValidator[a] && (a != b)) => (isBValidatorBefore == currentContract.isValidator[b]);
}

// removeValidator can remove a validator
rule removeValidatorFunctinality2()
{
    env e;
    allInvariants(e);
    
    address a;
    calldataarg args;
    bool isValidatorBefore = currentContract.isValidator[a];
    removeValidator(e, args);

    satisfy isValidatorBefore && !currentContract.isValidator[a];
}

// after removeValidator, a validator is unset, and quorum and step are updated
rule removeValidatorFunctinality3()
{
    env e;
    allInvariants(e);
    
    address a;
    uint256 newQuorum;
    uint256 step;
    removeValidator(e, a, newQuorum, step);

    assert !currentContract.isValidator[a] && currentContract.quorum == newQuorum && currentContract.step == step;
}

//  there is a case in which removeValidator decreases the count
rule removeValidatorFunctinality4()
{
    env e;
    allInvariants(e);
    
    calldataarg args;

    bytes32 transactionId;
    uint256 count = getConfirmationCount(transactionId);
    removeValidator(e, args);

    satisfy count - 1 == getConfirmationCount(transactionId);
}

// the count may be unimpacted by the removeValidator
rule removeValidatorFunctinality5()
{
    env e;
    allInvariants(e);
    
    calldataarg args;

    bytes32 transactionId;
    uint256 count = getConfirmationCount(transactionId);
    removeValidator(e, args);

    satisfy count == getConfirmationCount(transactionId);
}

// count must decrease or not change upon removeValidator
rule removeValidatorFunctinality6()
{
    env e;
    allInvariants(e);
    
    calldataarg args;

    bytes32 transactionId;
    uint256 count = getConfirmationCount(transactionId);
    removeValidator(e, args);

    assert count - 1 == getConfirmationCount(transactionId) || count == getConfirmationCount(transactionId);
}

// replaceValidator needs to be called by the contract
rule replaceValidatorCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    replaceValidator(e, args);
    assert e.msg.sender == currentContract;
}

// replaceValidator doesn't change quorum, doesn't change validator length
// and can remove at most one and add at most one validator
rule replaceValidatorFunctinality()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    address a;
    address b;
    uint256 lengthBefore = currentContract.validators.length;
    uint256 oldQuorum = currentContract.quorum;
    bool isAValidatorBefore = currentContract.isValidator[a];
    bool isBValidatorBefore = currentContract.isValidator[b];
    replaceValidator(e, args);
    assert lengthBefore == currentContract.validators.length;
    assert currentContract.quorum == oldQuorum;
    assert (isAValidatorBefore && !currentContract.isValidator[a] && (a != b)) => (isBValidatorBefore => currentContract.isValidator[b]);
    assert (!isAValidatorBefore && currentContract.isValidator[a] && (a != b)) => (!isBValidatorBefore => !currentContract.isValidator[b]);
}

// quorum can only be changed by the contract
rule changeQuorumCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    changeQuorum(e, args);
    assert e.msg.sender == currentContract;
}

// one needs to be the validator to invoke voteForTransaction
rule voteForTransactionCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    bool isValidatorBefore = currentContract.isValidator[e.msg.sender];
    voteForTransaction(e, args);
    assert isValidatorBefore;
}

// WE SHOULD BE ABLE TO INCREASE CONFIRMATION COUNT using voteForTransaction
rule voteForTransactionFunctinality()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;
    uint256 index;
    require index < currentContract.validators.length;
    require e.msg.sender == currentContract.validators[index];
    bool isExistedBefore = transactionExists(transactionId);
    address destinationBefore = currentContract.transactions[transactionId].destination;
    uint256 valueBefore = currentContract.transactions[transactionId].value;
    bytes dataBefore = getDataOfTransaction(transactionId);
    bool hasRewardBefore = currentContract.transactions[transactionId].hasReward;
    uint256 confirmationCountBefore = getConfirmationCount(transactionId);
    voteForTransaction(e, transactionId, destination, value, data, hasReward);
    uint256 confirmationCountAfter = getConfirmationCount(transactionId);
    assert (isExistedBefore && destinationBefore != currentContract) => transactionExists(transactionId);
    
    assert (isExistedBefore && transactionExists(transactionId)) => (
                                destinationBefore == currentContract.transactions[transactionId].destination &&
                                valueBefore == currentContract.transactions[transactionId].value &&
                                hash(dataBefore) == hash(getDataOfTransaction(transactionId)) &&
                                hasRewardBefore == currentContract.transactions[transactionId].hasReward
    );
    satisfy ((destinationBefore != currentContract) && (destination != currentContract)) && confirmationCountBefore + 1 == confirmationCountAfter;
}

// if the vote period is nonzero, the vote period is no less than the timestamp
rule voteForTransactionTime()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;
    requireInvariant VoteToChangeValidatorTransactionHasVotePeriod(e, transactionId);

    voteForTransaction(e, transactionId, destination, value, data, hasReward);
    assert currentContract.transactions[transactionId].validatorVotePeriod != 0 => e.block.timestamp <= currentContract.transactions[transactionId].validatorVotePeriod;
}

// can re-confirm after an execution
rule voteForTransactionExecute()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;
    bool isConfirmedBefore = isConfirmed(transactionId);
    bool isExecutedBefore = currentContract.transactions[transactionId].executed;
    voteForTransaction(e, transactionId, destination, value, data, hasReward);
    satisfy !isConfirmedBefore && isConfirmed(transactionId) && isExecutedBefore && currentContract.transactions[transactionId].executed;
}

// can confirm and its not executed regardless
rule voteForTransactionExecute2()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    address destination;
    uint256 value;
    bytes data;
    bool hasReward;
    bool isConfirmedBefore = isConfirmed(transactionId);
    bool isExecutedBefore = currentContract.transactions[transactionId].executed;
    voteForTransaction(e, transactionId, destination, value, data, hasReward);
    satisfy !isConfirmedBefore && isConfirmed(transactionId) && !isExecutedBefore && !currentContract.transactions[transactionId].executed;
}

// the executeTransaction tx sender can be arbitrary
rule executeTransactionCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    storage init = lastStorage;
    uint256 sum = require_uint256(rewardsPot() + WRAPPING_FEE());
    require sideRewardsPot() >= WRAPPING_FEE();
    executeTransaction(e, args);
    env e2;
    require (e.msg.value == e2.msg.value) && (e.block.timestamp == e2.block.timestamp);
    require e2.msg.sender != e.msg.sender;
    executeTransaction@withrevert(e2, args) at init;
    assert !lastReverted;
}

// if executeTransation succeeds and the transaction was executed, it must have been confirmed
rule executeTransactionConfirmed()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;

    bool isConfirmedBefore = isConfirmed(transactionId);
    executeTransaction(e, transactionId);
    assert currentContract.transactions[transactionId].executed => isConfirmedBefore;
}

// must be a scenario where the vote count decreases for the transaction not to be confirmed after the execution
rule executeTransactionMayNotConfirmedAfter()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    executeTransaction(e, transactionId);
    satisfy currentContract.transactions[transactionId].executed && !isConfirmed(transactionId);
}

// executeTransaction must fail if the transaction is executed
// if has rewards, WRAPPING FEE needs to be included in the value
// must send msg.value to the function at least of tx.value
rule executeTransactionFee()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    bool executedBefore = currentContract.transactions[transactionId].executed;
    uint256 balanceBefore = nativeBalances[currentContract];
    uint256 rewardsPotBefore = rewardsPot();
    executeTransaction(e, transactionId);
    assert !executedBefore;
    assert (currentContract.transactions[transactionId].executed && 
            currentContract.transactions[transactionId].hasReward) => (
                currentContract.transactions[transactionId].value >= WRAPPING_FEE() &&
                rewardsPotBefore + WRAPPING_FEE() <= rewardsPot()
            );
    assert (currentContract.transactions[transactionId].destination != currentContract && currentContract.transactions[transactionId].executed) => (to_mathint(balanceBefore) - to_mathint(nativeBalances[currentContract])) <= currentContract.transactions[transactionId].value;
}

// 
rule removeTransactionCaller()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    removeTransaction(e, args);
    assert e.msg.sender == currentContract;
}

rule removeTransactionFunctinality()
{
    env e;
    allInvariants(e);
    
    bytes32 transactionId;
    bool isExistedBefore = currentContract.transactions[transactionId].destination != 0;
    uint256 lengthBefore = currentContract.transactionIds.length;

    removeTransaction(e, transactionId);
    assert isExistedBefore && currentContract.transactions[transactionId].destination == 0;
    assert lengthBefore - 1 == currentContract.transactionIds.length;
}

// rewards pot evenly distributes, leaving remainder and the last withdarawal time is updated
rule distributeRewardsValueAfter()
{
    env e;
    allInvariants(e);
    
    calldataarg args;
    uint256 oldRewards;
    require oldRewards == rewardsPot();
    require currentContract.validators.length != 1;
    distributeRewards(e, args);
    assert lastWithdrawalTime() == e.block.timestamp;
    assert rewardsPot() == oldRewards % (currentContract.validators.length - 1);
}


invariant uniqenessValidators(env e)
    forall uint256 i. forall uint256 j. (j < currentContract.validators.length && i < j) => currentContract.validators[i] != currentContract.validators[j]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant reverseMapNotZero_IFF_IsValidator(env e)
    forall address a. currentContract.validatorsReverseMap[a] != 0 <=> currentContract.isValidator[a]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorNotZero(env e)
    forall uint256 i. (i != 0 && i < currentContract.validators.length) <=> currentContract.validators[i] != 0
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorNotThis(env e)
    forall uint256 i. (i < currentContract.validators.length) => currentContract.validators[i] != currentContract
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorsSetToZero(env e)
    forall uint256 i. i >= currentContract.validators.length => currentContract.validators[i] == 0
{
    preserved
    {
        allInvariants(e);
    }
}

invariant zeroNotValidator(env e)
    !currentContract.isValidator[0]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant thisNotValidator(env e)
    !currentContract.isValidator[currentContract]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant zeroIsInValidatorsZero(env e)
    require_uint256(currentContract.validators[0]) == 0
{
    preserved
    {
        allInvariants(e);
    }
}

invariant lengthIsNotZero(env e)
    (currentContract.validators.length != 0) && (currentContract.transactionIds.length != 0)
{
    preserved
    {
        allInvariants(e);
    }
}


invariant validatorIsValid(env e)
    forall uint256 i. (i != 0 && i < currentContract.validators.length) <=> currentContract.isValidator[currentContract.validators[i]]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorsReverseMapValid(env e)
    forall uint256 i. (i < currentContract.validators.length => currentContract.validatorsReverseMap[currentContract.validators[i]] == i)
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorsReverseMapValidValue(env e)
    forall address a. currentContract.validatorsReverseMap[a] < currentContract.validators.length
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorsReverseMapReverse(env e)
    forall address a. currentContract.validatorsReverseMap[a] != 0 => currentContract.validators[currentContract.validatorsReverseMap[a]] == a
{
    preserved
    {
        allInvariants(e);
    }
}

invariant validatorsReverseMapUniqeness(env e)
    forall address a. forall address b. (a != b && currentContract.validatorsReverseMap[a] != 0 && currentContract.validatorsReverseMap[b] != 0) => currentContract.validatorsReverseMap[a] != currentContract.validatorsReverseMap[b]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant uniqenessTransactionIds(env e)
    forall uint256 i. forall uint256 j. (j < currentContract.transactionIds.length && i < j) => currentContract.transactionIds[i] != currentContract.transactionIds[j]
{
    preserved
    {
        allInvariants(e);
    }
}

invariant zeroInTransactionIdsZero(env e)
    currentContract.transactionIds[0] == to_bytes32(0)
{
    preserved
    {
        allInvariants(e);
    }
}
invariant transactionIdsReverseMapZeroIsZero(env e)
    currentContract.transactionIdsReverseMap[to_bytes32(0)] == 0
{
    preserved
    {
        allInvariants(e);
    }
}

invariant zeroNotInTransactionIds(env e)
    forall uint256 i. (i != 0 && i < currentContract.transactionIds.length) => (currentContract.transactionIds[i] != to_bytes32(0))
{
    preserved
    {
        allInvariants(e);
    }
}

invariant transactionIdsReverseMapValid(env e)
    (forall uint256 i. (i < currentContract.transactionIds.length => currentContract.transactionIdsReverseMap[currentContract.transactionIds[i]] == i)) &&
    (forall bytes32 id. (((currentContract.transactionIdsReverseMap[id] != 0) => (currentContract.transactionIds[currentContract.transactionIdsReverseMap[id]] == id)) && (currentContract.transactionIdsReverseMap[id] < currentContract.transactionIds.length))) &&
    (forall bytes32 id. currentContract.transactionIdsReverseMap[id] != 0 <=> (currentContract.transactions[id].destination != 0))
{
    preserved
    {
        allInvariants(e);
    }
}

invariant zeroInTransactionIdsLength(env e)
    forall uint256 i. i >= currentContract.transactionIds.length => currentContract.transactionIds[i] == to_bytes32(0)
{
    preserved
    {
        allInvariants(e);
    }
}

invariant transactionIdIsValid(env e)
    forall uint256 i. (i != 0 && i < currentContract.transactionIds.length) <=> currentContract.transactions[currentContract.transactionIds[i]].destination != 0
{
    preserved
    {
        allInvariants(e);
    }
}

invariant quorumIsValid(env e)
    currentContract.quorum <= currentContract.validators.length && currentContract.quorum != 0 && fib[currentContract.step] == currentContract.quorum
{
    preserved
    {
        allInvariants(e);
    }
}

invariant VoteToChangeValidatorTransactionHasVotePeriod(env e, bytes32 transactionId)
    isVoteToChangeValidator(getDataOfTransaction(transactionId), currentContract.transactions[transactionId].destination) <=> currentContract.transactions[transactionId].validatorVotePeriod != 0
{
    preserved
    {
        allInvariants(e);
    }
}
invariant emptyTransactionsIsEmpty(env e, bytes32 transactionId)
    currentContract.transactions[transactionId].destination == 0 => 
    (getConfirmationCount(transactionId) == 0 &&
    (currentContract.transactions[transactionId].value == 0 && 
    getDataOfTransaction(transactionId).length == 0 && 
    currentContract.transactions[transactionId].hasReward == false && 
    currentContract.transactions[transactionId].validatorVotePeriod == 0 &&
    currentContract.transactions[transactionId].executed == false))
{
    preserved with (env e2)
    {
        require e2.block.timestamp == e.block.timestamp;
        allInvariants(e);
    }
}

invariant canPayRewardsPot(env e)
    nativeBalances[currentContract] >= require_uint256(rewardsPot() + sideRewardsPot() + usersValue())
{
    preserved
    {
        allInvariants(e);
    }
}