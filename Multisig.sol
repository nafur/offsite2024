pragma solidity ^0.8.7;

import "./State.sol";

contract Multisig is State {

    function fib(uint256 i) pure private returns (uint256) {
        if (i == 0) return 1;
        if (i == 1) return 1;
        if (i == 2) return 2;
        if (i == 3) return 3;
        if (i == 4) return 5;
        if (i == 5) return 8;
        if (i == 6) return 13;
        if (i == 7) return 21;
        if (i == 8) return 34;
        if (i == 9) return 55;
        if (i == 10) return 89;
        if (i == 11) return 144;
        if (i == 12) return 233;
        if (i == 13) return 377;
        if (i == 14) return 610;
        if (i == 15) return 987;
        if (i == 16) return 1597;
        if (i == 17) return 2584;
        if (i == 18) return 4181;
        if (i == 19) return 6765;

        uint256 last = 1;
        uint256 res = 1;
        while (i > 1) {
            (last, res) = (res, last + res);
            i -= 1;
        }
        return res;
    }

    function isVoteToChangeValidator(bytes calldata data, address destination)
        public
        view
        returns (bool)
    {
        if (data.length > 4) {
            return
                (bytes4(data[:4]) == this.addValidator.selector || bytes4(data[:4]) == this.replaceValidator.selector || bytes4(data[:4]) == this.removeValidator.selector) &&
                destination == address(this);
        }

        return false;
    }
    
    modifier reentracy(){
        require(guard == 1);
        guard = 2;
        _;
        guard = 1;
    }

    modifier reentracyChack(){
        require(guard == 1);
        _;
    }
    constructor(address[] memory newValidators,  uint256 _quorum, uint256 _step)
    {
        // add sentinel at zero
        validators.push(address(0));
        for (uint256 i = 0; i < newValidators.length; i++) {
            require(!isValidator[newValidators[i]]);
            require(newValidators[i] != address(0));
            require(newValidators[i] != address(this));
            
            validatorsReverseMap[newValidators[i]] = validators.length;
            validators.push(newValidators[i]);
            isValidator[newValidators[i]] = true;
        }

        changeQuorum(_quorum, _step);

        // add sentinel at zero
        transactionIds.push(0);
    }

    function addValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public   {
        require(msg.sender == address(this));
        require(validator != address(0));
        require(validator != address(this));
        require(!isValidator[validator]);
        validatorsReverseMap[validator] = validators.length;
        validators.push(validator);
        isValidator[validator] = true;

        changeQuorum(newQuorum, _step);

        // make sure there are no confirmations for this validator yet
        for (uint256 tid = 1; tid < transactionIds.length; tid++) {
            require(!confirmations[transactionIds[tid]][validator]);
        }
    }


    function removeValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public {
        require(msg.sender == address(this));
        require(isValidator[validator]);
        uint256 id = validatorsReverseMap[validator];
        validators[id] = validators[validators.length - 1];
        validatorsReverseMap[validators[id]] = id;
        validators.pop();
        delete validatorsReverseMap[validator];
        delete isValidator[validator];

        changeQuorum(newQuorum, _step);

        for (uint256 tid = 1; tid < transactionIds.length; tid++) {
            delete confirmations[transactionIds[tid]][validator];
        }
    }


    function replaceValidator(
        address validator,
        address newValidator
    )
        public
    {
        require(msg.sender == address(this));
        require(newValidator != address(0));
        require(newValidator != address(this));
        require(isValidator[validator]);
        require(!isValidator[newValidator]);
        validators[validatorsReverseMap[validator]] = newValidator;

        validatorsReverseMap[newValidator] = validatorsReverseMap[validator];
        delete validatorsReverseMap[validator];
        isValidator[newValidator] = true;
        delete isValidator[validator];
        
        for (uint256 tid = 1; tid < transactionIds.length; tid++) {
            bytes32 t = transactionIds[tid];
            if (confirmations[t][validator]) {
                delete confirmations[t][validator];
                confirmations[t][newValidator] = true;
            }
        }
    }

    function changeQuorum(uint256 _quorum, uint256 _step)
        public
    {
        require(msg.sender == address(this));
        require(_quorum == fib(_step));
        require(_quorum < validators.length);
        quorum = _quorum;
        step = _step;
    }

    function transactionExists(bytes32 transactionId)
        public
        view
        returns (bool)
    {
        require(transactionIdsReverseMap[transactionId] != 0);
        return transactionIds[transactionIdsReverseMap[transactionId]] == transactionId;
    }

    function voteForTransaction(
        bytes32 transactionId,
        address destination,
        uint256 value,
        bytes calldata data,
        bool hasReward
    ) public payable {
        require(isValidator[msg.sender]);
        require(!confirmations[transactionId][msg.sender]);

        if (transactionExists(transactionId)) {
            require(!transactions[transactionId].executed);
            if (isVoteToChangeValidator(data, destination)) {
                require(block.timestamp <= transactions[transactionId].validatorVotePeriod);
            }
        } else {
            transactions[transactionId] = Transaction({
                destination: destination,
                value: value,
                data: data,
                executed: false,
                hasReward: hasReward,
                validatorVotePeriod: isVoteToChangeValidator(data, destination) ? (block.timestamp + ADD_VALIDATOR_VOTE_PERIOD) : 0
            });
            transactionIdsReverseMap[transactionId] = transactionIds.length;
            transactionIds.push(transactionId);
        }

        confirmations[transactionId][msg.sender] = true;
        if (isConfirmed(transactionId)) {
            executeTransaction(transactionId);
        }
    }

    function executeTransaction(bytes32 transactionId) public
    {
        require(transactionExists(transactionId));
        require(isConfirmed(transactionId));
        Transaction storage trans = transactions[transactionId];
        require(trans.executed == false);
        (bool success,) = trans.destination.call{value: trans.value}(trans.data);
        trans.executed = true;
        require(success);
    }

    function removeTransaction(bytes32 transactionId) public {
    }

    function isConfirmed(bytes32 transactionId) public view returns (bool) {
        return getConfirmationCount(transactionId) >= quorum;
    }

    function getDataOfTransaction(bytes32 id) external view returns (bytes memory data){
        data = transactions[id].data;
    }

    function hash(bytes memory data) external pure returns (bytes32 result)
    {
        result = keccak256(data);
    }

    function getConfirmationCount(bytes32 transactionId)
        public
        view
        returns (uint256 count)
    {
        require(transactionExists(transactionId));
        count = 0;
        for (uint256 vid = 1; vid < validators.length; vid++) {
            if (confirmations[transactionId][validators[vid]]) count++;
        }
    }

    function distributeRewards() public reentracy
    {
    }
}
