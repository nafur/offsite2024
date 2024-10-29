pragma solidity ^0.8.7;

import "./State.sol";

contract Multisig is State {

    uint256[8] private fibonacciNumbers = [1, 1, 2, 3, 5, 8, 13, 21];

    function getFibonacci(uint256 n) internal view returns (uint256) {
        require(n < 8, "Step too large");
        return fibonacciNumbers[n];
    }

    constructor(address[] memory newValidators, uint256 _quorum, uint256 _step) {
        require(_quorum > 0 && _quorum <= newValidators.length);
        require(_step < 8, "Step too large");
        require(getFibonacci(_step) == _quorum, "Quorum must match Fibonacci number"); 
        
        // Initialize with zero address at index 0
        validators.push(address(0));
        transactionIds.push(bytes32(0));
        guard = 1;
        
        quorum = _quorum;
        step = _step;
        
        for (uint256 i = 0; i < newValidators.length; i++) {
            require(newValidators[i] != address(0) && newValidators[i] != address(this));
            require(!isValidator[newValidators[i]]);
            
            validators.push(newValidators[i]);
            validatorsReverseMap[newValidators[i]] = validators.length - 1;
            isValidator[newValidators[i]] = true;
        }
    }

    function isVoteToChangeValidator(bytes calldata data, address destination)
        public
        view
        returns (bool)
    {
        if (data.length > 4) {
            return
                (bytes4(data[:4]) == this.addValidator.selector || 
                 bytes4(data[:4]) == this.replaceValidator.selector || 
                 bytes4(data[:4]) == this.removeValidator.selector) &&
                destination == address(this);
        }
        return false;
    }

    modifier onlyContract() {
        require(msg.sender == address(this));
        _;
    }

    modifier onlyValidator() {
        require(isValidator[msg.sender]);
        _;
    }
    
    modifier reentracy() {
        require(guard == 1);
        guard = 2;
        _;
        guard = 1;
    }

    function addValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public onlyContract {
        require(validator != address(0) && validator != address(this));
        require(!isValidator[validator]);
        require(getFibonacci(_step) == newQuorum);
        require(newQuorum <= validators.length + 1);
        
        validatorsReverseMap[validator] = validators.length;
        validators.push(validator);
        isValidator[validator] = true;
        
        changeQuorum(newQuorum, _step);
    }

    function removeValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public onlyContract {
        require(isValidator[validator]);
        require(getFibonacci(_step) == newQuorum);
        require(newQuorum <= validators.length - 1);
        
        uint256 index = validatorsReverseMap[validator];
        uint256 lastIndex = validators.length - 1;
        
        if (index != lastIndex) {
            address lastValidator = validators[lastIndex];
            validators[index] = lastValidator;
            validatorsReverseMap[lastValidator] = index;
        }
        
        validators.pop();
        delete validatorsReverseMap[validator];
        delete isValidator[validator];
        
        quorum = newQuorum;
        step = _step;
        
        // Update confirmations for all transactions
        for (uint i = 1; i < transactionIds.length; i++) {
            bytes32 txId = transactionIds[i];
            if (confirmations[txId][validator]) {
                confirmations[txId][validator] = false;
            }
        }
    }

    function changeQuorum(uint256 _quorum, uint256 _step) public onlyContract {
        require(_quorum <= validators.length);
        require(getFibonacci(_step) == _quorum);
        quorum = _quorum;
        step = _step;
    }

    function replaceValidator(
        address validator,
        address newValidator
    ) public onlyContract {
        require(validator != address(0) && newValidator != address(0));
        require(validator != address(this) && newValidator != address(this));
        require(isValidator[validator]);
        require(!isValidator[newValidator]);
        
        uint256 index = validatorsReverseMap[validator];
        validators[index] = newValidator;
        validatorsReverseMap[newValidator] = index;
        isValidator[newValidator] = true;
        
        delete validatorsReverseMap[validator];
        delete isValidator[validator];
        
        // Transfer confirmations
        for (uint i = 1; i < transactionIds.length; i++) {
            bytes32 txId = transactionIds[i];
            if (confirmations[txId][validator]) {
                confirmations[txId][newValidator] = true;
                confirmations[txId][validator] = false;
            }
        }
    }


    function transactionExists(bytes32 transactionId)
        public
        view
        returns (bool)
    {
        return transactions[transactionId].destination != address(0);
    }

    function getConfirmationCount(bytes32 transactionId)
        public
        view
        returns (uint256 count)
    {
        for (uint i = 1; i < validators.length; i++) {
            if (confirmations[transactionId][validators[i]]) {
                count++;
            }
        }
    }

    function isConfirmed(bytes32 transactionId) public view returns (bool) {
        return getConfirmationCount(transactionId) >= quorum;
    }

    function voteForTransaction(
        bytes32 transactionId,
        address destination,
        uint256 value,
        bytes calldata data,
        bool hasReward
    ) public payable onlyValidator {
        require(destination != address(0));
        
        if (!transactionExists(transactionId)) {
            transactions[transactionId] = Transaction({
                destination: destination,
                value: value,
                data: data,
                executed: false,
                hasReward: hasReward,
                validatorVotePeriod: isVoteToChangeValidator(data, destination) ? block.timestamp + ADD_VALIDATOR_VOTE_PERIOD : 0
            });
            transactionIds.push(transactionId);
            transactionIdsReverseMap[transactionId] = transactionIds.length - 1;
        } else {
            require(!transactions[transactionId].executed);
            if (transactions[transactionId].validatorVotePeriod != 0) {
                require(block.timestamp <= transactions[transactionId].validatorVotePeriod);
            }
        }
        
        if (!confirmations[transactionId][msg.sender]) {
            confirmations[transactionId][msg.sender] = true;
            if (isConfirmed(transactionId)) {
                executeTransaction(transactionId);
            }
        }
    }

    function executeTransaction(bytes32 transactionId) public {
        require(transactionExists(transactionId));
        require(!transactions[transactionId].executed);
        require(isConfirmed(transactionId));
        
        Transaction storage txn = transactions[transactionId];
        
        if (txn.hasReward) {
            require(txn.value >= WRAPPING_FEE);
            rewardsPot += WRAPPING_FEE;
        }
        
        txn.executed = true;
        
        if (txn.destination != address(this)) {
            (bool success,) = txn.destination.call{value: txn.value}(txn.data);
            require(success);
        } else {
            (bool success,) = txn.destination.call(txn.data);
            require(success);
        }
    }

    function removeTransaction(bytes32 transactionId) public onlyContract {
        require(transactionExists(transactionId));
        
        uint256 index = transactionIdsReverseMap[transactionId];
        uint256 lastIndex = transactionIds.length - 1;
        
        if (index != lastIndex) {
            bytes32 lastTxId = transactionIds[lastIndex];
            transactionIds[index] = lastTxId;
            transactionIdsReverseMap[lastTxId] = index;
        }
        
        transactionIds.pop();
        delete transactionIdsReverseMap[transactionId];
        delete transactions[transactionId];
    }

    function distributeRewards() public reentracy {
        require(validators.length > 1);
        
        uint256 rewardsToDistribute = rewardsPot;
        uint256 validatorCount = validators.length - 1;
        uint256 remainder = rewardsToDistribute % validatorCount;
        uint256 rewardPerValidator = rewardsToDistribute / validatorCount;
        
        rewardsPot = remainder;
        lastWithdrawalTime = block.timestamp;
        
        for (uint i = 1; i < validators.length; i++) {
            (bool success,) = validators[i].call{value: rewardPerValidator}("");
            require(success);
        }
    }

    function getDataOfTransaction(bytes32 id) external view returns (bytes memory data) {
        data = transactions[id].data;
    }

    function hash(bytes memory data) external pure returns (bytes32 result) {
        result = keccak256(data);
    }
}