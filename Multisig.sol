pragma solidity ^0.8.7;

import "./State.sol";

contract Multisig is State {

    function fib(uint256 i) pure private returns (uint256) {
        if (i == 0) return 0;
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
    }


    function removeValidator(
        address validator,
        uint256 newQuorum,
        uint256 _step
    ) public {
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

    }

    function distributeRewards() public reentracy
    {
    }
}