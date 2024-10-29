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
    }

    function addValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public   {
        require(msg.sender == address(this));
        require(!isValidator[validator]);
        validatorsReverseMap[validator] = validators.length;
        validators.push(validator);
        isValidator[validator] = true;

        changeQuorum(newQuorum, _step);

        // make sure there are no confirmations for this validator yet
        for (uint256 tid = 0; tid < transactionIds.length; tid++) {
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

        for (uint256 tid = 0; tid < transactionIds.length; tid++) {
            delete confirmations[transactionIds[tid]][validator];
        }
    }


    function replaceValidator(
        address validator,
        address newValidator
    )
        public
    {}

    function changeQuorum(uint256 _quorum, uint256 _step)
        public
    {
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
    }

    function voteForTransaction(
        bytes32 transactionId,
        address destination,
        uint256 value,
        bytes calldata data,
        bool hasReward
    ) public payable {
    }

    function executeTransaction(bytes32 transactionId) public
    {
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
        require(transactionIds[transactionIdsReverseMap[transactionId]] == transactionId);
        count = 0;
        for (uint256 vid = 0; vid < validators.length; vid++) {
            if (confirmations[transactionId][validators[vid]]) count++;
        }
    }

    function distributeRewards() public reentracy
    {
    }
}