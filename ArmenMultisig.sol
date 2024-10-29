pragma solidity ^0.8.7;

import "./State.sol";

contract Multisig is State {

    modifier onlyValidator() {
        require(isValidator[msg.sender], "Not a validator");
        _;
    }

    modifier onlyContract() {
        require(msg.sender == address(this), "Only contract can call");
        _;
    }

    modifier reentracy() {
        require(guard == 1, "Reentrant call");
        guard = 2;
        _;
        guard = 1;
    }

    function getFibonacci(uint256 i) internal view returns (uint256) {
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
        if (data.length >= 4) {
            bytes4 selector = bytes4(data[:4]);
            return (selector == this.addValidator.selector || 
                   selector == this.replaceValidator.selector || 
                   selector == this.removeValidator.selector) &&
                   destination == address(this);
        }
        return false;
    }

    function addValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public onlyContract {
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

    function changeQuorum(uint256 _quorum, uint256 _step) public onlyContract {
        require(_quorum == getFibonacci(_step));
        require(_quorum < validators.length);
        quorum = _quorum;
        step = _step;
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
            uint256 votePeriod = isVoteToChangeValidator(data, destination) ? 
                                block.timestamp + ADD_VALIDATOR_VOTE_PERIOD : 0;
            
            transactions[transactionId] = Transaction({
                destination: destination,
                value: value,
                data: data,
                executed: false,
                hasReward: hasReward,
                validatorVotePeriod: votePeriod
            });
            transactionIds.push(transactionId);
            transactionIdsReverseMap[transactionId] = transactionIds.length - 1;
        } else {
            require(!transactions[transactionId].executed, "Transaction already executed");
            if (transactions[transactionId].validatorVotePeriod != 0) {
                require(block.timestamp <= transactions[transactionId].validatorVotePeriod, "Vote period expired");
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
        require(transactionExists(transactionId), "Transaction does not exist");
        require(!transactions[transactionId].executed, "Transaction already executed");
        require(isConfirmed(transactionId), "Transaction not confirmed");
        
        Transaction storage txn = transactions[transactionId];
        
        if (txn.hasReward) {
            require(txn.value >= WRAPPING_FEE, "Insufficient fee");
            rewardsPot += WRAPPING_FEE;
            usersValue += txn.value - WRAPPING_FEE;
        } else {
            usersValue += txn.value;
        }
        
        txn.executed = true;
        
        (bool success,) = txn.destination.call{value: txn.value}(txn.data);
        require(success, "Transaction execution failed");
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
        require(validators.length > 1, "No validators to distribute to");
        
        uint256 rewardsToDistribute = rewardsPot;
        uint256 validatorCount = validators.length - 1;
        uint256 remainder = rewardsToDistribute % validatorCount;
        uint256 rewardPerValidator = rewardsToDistribute / validatorCount;
        
        rewardsPot = remainder;
        lastWithdrawalTime = block.timestamp;
        
        for (uint i = 1; i < validators.length; i++) {
            (bool success,) = validators[i].call{value: rewardPerValidator}("");
            require(success, "Reward transfer failed");
        }
    }

    function transactionExists(bytes32 transactionId) public view returns (bool) {
        return transactions[transactionId].destination != address(0);
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

    function isConfirmed(bytes32 transactionId) public view returns (bool) {
        return getConfirmationCount(transactionId) >= quorum;
    }

    function getDataOfTransaction(bytes32 id) external view returns (bytes memory data) {
        data = transactions[id].data;
    }

    function hash(bytes memory data) external pure returns (bytes32 result) {
        result = keccak256(data);
    }
}