// class_hash: 0x33c3f6fa91eccdaec91535bbd052ee66434b2a6cd8c2003c5ff54c759e12c23

use array::{ArrayTrait};
use debug::{PrintTrait};
use option::{Option, OptionTrait};
use starknet::storage_access::{StorePacking};
use zeroable::{Zeroable};
use hash::{HashStateTrait, Hash};

#[derive(Copy, Drop, Serde)]
struct i129 {
    mag: u128,
    sign: bool,
}

#[generate_trait]
impl i129TraitImpl of i129Trait {
    fn is_negative(self: i129) -> bool {
        self.sign & (Zeroable::is_non_zero(self))
    }
}

#[inline(always)]
fn i129_new(mag: u128, sign: bool) -> i129 {
    i129 { mag, sign: sign & (mag != 0) }
}

impl i129Zeroable of Zeroable<i129> {
    fn zero() -> i129 {
        i129 { mag: 0, sign: false }
    }

    fn is_zero(self: i129) -> bool {
        Zeroable::is_zero(self)
    }

    fn is_non_zero(self: i129) -> bool {
        Zeroable::is_non_zero(self)
    }
}

impl i129PrintTrait of PrintTrait<i129> {
    fn print(self: i129) {
        self.sign.print();
        self.mag.print();
    }
}

impl u128IntoI129 of Into<u128, i129> {
    fn into(self: u128) -> i129 {
        i129 { mag: self, sign: false }
    }
}

impl i129TryIntoU128 of TryInto<i129, u128> {
    fn try_into(self: i129) -> Option<u128> {
        if (self.is_negative()) {
            Option::None(())
        } else {
            Option::Some(self.mag)
        }
    }
}

#[generate_trait]
impl AddDeltaImpl of AddDeltaTrait {
    fn add(self: u128, delta: i129) -> u128 {
        (self.into() + delta).try_into().expect('ADD_DELTA')
    }

    fn sub(self: u128, delta: i129) -> u128 {
        (self.into() - delta).try_into().expect('SUB_DELTA')
    }
}

impl HashI129<S, +HashStateTrait<S>, +Drop<S>> of Hash<i129, S> {
    #[inline(always)]
    fn update_state(state: S, value: i129) -> S {
        let mut hashable: felt252 = value.mag.into();
        if value.is_negative() {
            hashable += 0x100000000000000000000000000000000; // 2**128
        }

        state.update(hashable)
    }
}

impl i129StorePacking of StorePacking<i129, felt252> {
    fn pack(value: i129) -> felt252 {
        assert(value.mag < 0x80000000000000000000000000000000, 'i129_store_overflow');
        if (value.sign) {
            -value.mag.into()
        } else {
            value.mag.into()
        }
    }
    fn unpack(value: felt252) -> i129 {
        if value.into() >= 0x80000000000000000000000000000000_u256 {
            i129_new((-value).try_into().unwrap(), true)
        } else {
            i129_new(value.try_into().unwrap(), false)
        }
    }
}

impl i129Add of Add<i129> {
    fn add(lhs: i129, rhs: i129) -> i129 {
        i129_add(lhs, rhs)
    }
}

impl i129AddEq of AddEq<i129> {
    #[inline(always)]
    fn add_eq(ref self: i129, other: i129) {
        self = Add::add(self, other);
    }
}

impl i129Sub of Sub<i129> {
    fn sub(lhs: i129, rhs: i129) -> i129 {
        i129_sub(lhs, rhs)
    }
}

impl i129SubEq of SubEq<i129> {
    #[inline(always)]
    fn sub_eq(ref self: i129, other: i129) {
        self = Sub::sub(self, other);
    }
}

impl i129Div of Div<i129> {
    fn div(lhs: i129, rhs: i129) -> i129 {
        i129_div(lhs, rhs)
    }
}

impl i129DivEq of DivEq<i129> {
    #[inline(always)]
    fn div_eq(ref self: i129, other: i129) {
        self = Div::div(self, other);
    }
}

impl i129PartialEq of PartialEq<i129> {
    fn eq(lhs: @i129, rhs: @i129) -> bool {
        i129_eq(lhs, rhs)
    }

    fn ne(lhs: @i129, rhs: @i129) -> bool {
        !i129_eq(lhs, rhs)
    }
}

impl i129PartialOrd of PartialOrd<i129> {
    fn le(lhs: i129, rhs: i129) -> bool {
        i129_le(lhs, rhs)
    }
    fn ge(lhs: i129, rhs: i129) -> bool {
        i129_ge(lhs, rhs)
    }

    fn lt(lhs: i129, rhs: i129) -> bool {
        i129_lt(lhs, rhs)
    }
    fn gt(lhs: i129, rhs: i129) -> bool {
        i129_gt(lhs, rhs)
    }
}

impl i129Neg of Neg<i129> {
    fn neg(a: i129) -> i129 {
        i129_neg(a)
    }
}

fn i129_add(a: i129, b: i129) -> i129 {
    if a.sign == b.sign {
        i129_new(a.mag + b.mag, a.sign)
    } else {
        let (larger, smaller) = if a.mag >= b.mag {
            (a, b)
        } else {
            (b, a)
        };
        let difference = larger.mag - smaller.mag;

        i129_new(difference, larger.sign)
    }
}

#[inline(always)]
fn i129_sub(a: i129, b: i129) -> i129 {
    a + i129_new(b.mag, !b.sign)
}

#[inline(always)]
fn i129_mul(a: i129, b: i129) -> i129 {
    i129_new(a.mag * b.mag, a.sign ^ b.sign)
}

#[inline(always)]
fn i129_div(a: i129, b: i129) -> i129 {
    i129_new(a.mag / b.mag, a.sign ^ b.sign)
}

#[inline(always)]
fn i129_eq(a: @i129, b: @i129) -> bool {
    (a.mag == b.mag) & ((a.sign == b.sign) | (*a.mag == 0))
}

fn i129_gt(a: i129, b: i129) -> bool {
    if (a.sign & !b.sign) {
        return false;
    }
    if (!a.sign & b.sign) {
        // return false iff both are zero
        return (Zeroable::is_non_zero(a)) | (Zeroable::is_non_zero(b));
    }
    if (a.sign & b.sign) {
        return a.mag < b.mag;
    } else {
        return a.mag > b.mag;
    }
}

#[inline(always)]
fn i129_ge(a: i129, b: i129) -> bool {
    (i129_eq(@a, @b) | i129_gt(a, b))
}

#[inline(always)]
fn i129_lt(a: i129, b: i129) -> bool {
    return !i129_ge(a, b);
}

#[inline(always)]
fn i129_le(a: i129, b: i129) -> bool {
    !i129_gt(a, b)
}

#[inline(always)]
fn i129_neg(x: i129) -> i129 {
    i129_new(x.mag, !x.sign)
}

#[derive(Copy, Drop, Serde, PartialEq, Hash, starknet::Store)]
struct Bounds {
    lower: i129,
    upper: i129
}

#[derive(Copy, Drop, Serde, PartialEq)]
struct CallPoints {
    after_initialize_pool: bool,
    before_swap: bool,
    after_swap: bool,
    before_update_position: bool,
    after_update_position: bool,
}

#[derive(Copy, Drop, Serde, PartialEq)]
struct GetTokenInfoResult {
    pool_price: PoolPrice,
    liquidity: u128,
    amount0: u128,
    amount1: u128,
    fees0: u128,
    fees1: u128,
}

#[derive(Copy, Drop, Serde, PartialEq, Hash, starknet::Store)]
struct PoolKey {
    token0: starknet::ContractAddress,
    token1: starknet::ContractAddress,
    fee: u128,
    tick_spacing: u128,
    extension: starknet::ContractAddress,
}

#[derive(Copy, Drop, Serde, PartialEq)]
struct PoolPrice {
    sqrt_ratio: u256,
    tick: i129,
    call_points: CallPoints,
}

#[starknet::interface]
trait IPositions<TStorage> {
    fn collect_fees(ref self: TStorage, id: u64, pool_key: PoolKey, bounds: Bounds) -> (u128, u128);
    fn get_nft_address(self: @TStorage) -> starknet::ContractAddress;
    fn get_token_info(
        self: @TStorage, id: u64, pool_key: PoolKey, bounds: Bounds
    ) -> GetTokenInfoResult;
}

#[starknet::interface]
trait IGrailsLocker<TState> {
    fn collectFees(ref self: TState, id: u64) -> (u128, u128);
    fn lock(
        ref self: TState,
        id: u64,
        unlockTimestamp: u64,
        poolKey: PoolKey,
        bounds: Bounds,
        operator: starknet::ContractAddress
    );
    fn operator(self: @TState, id: u64) -> starknet::ContractAddress;
    fn positionsContract(self: @TState) -> starknet::ContractAddress;
    fn positionsNFTContract(self: @TState) -> starknet::ContractAddress;
    fn transferOperator(ref self: TState, id: u64, newOperator: starknet::ContractAddress);
    fn unlock(ref self: TState, id: u64);
}

#[starknet::contract]
mod GrailsLocker {
    use openzeppelin::token::erc20::{ERC20ABIDispatcher, ERC20ABIDispatcherTrait};
    use openzeppelin::token::erc721::interface::{IERC721Dispatcher, IERC721DispatcherTrait};
    use starknet::{ContractAddress, get_block_timestamp, get_caller_address, get_contract_address};
    use super::{Bounds, IPositionsDispatcher, IPositionsDispatcherTrait, PoolKey};

    #[storage]
    struct Storage {
        operators: LegacyMap<u64, ContractAddress>,
        positions: LegacyMap<u64, Position>,
        nftContractDispatcher: IERC721Dispatcher,
        positionsDispatcher: IPositionsDispatcher
    }

    #[derive(Drop, Destruct, starknet::Store)]
    struct Position {
        unlock: u64,
        poolKey: PoolKey,
        bounds: Bounds
    }

    #[event]
    #[derive(Drop, starknet::Event)]
    enum Event {
        CollectFees: CollectFees,
        TransferOperator: TransferOperator
    }

    #[derive(Drop, starknet::Event)]
    struct CollectFees {
        #[key]
        id: u64,
        fees0: u128,
        fees1: u128
    }

    #[derive(Drop, starknet::Event)]
    struct TransferOperator {
        #[key]
        id: u64,
        #[key]
        previousOperator: ContractAddress,
        #[key]
        newOperator: ContractAddress
    }

    mod Errors {
        const INVALID_OPERATOR: felt252 = 'Invalid operator address';
        const STILL_LOCKED: felt252 = 'Position is still locked';
        const UNAUTHORIZED: felt252 = 'Unauthorized';
    }

    #[constructor]
    fn constructor(ref self: ContractState) {
        self
            .positionsDispatcher
            .write(
                IPositionsDispatcher {
                    contract_address: 0x02e0af29598b407c8716b17f6d2795eca1b471413fa03fb145a5e33722184067
                        .try_into()
                        .unwrap()
                }
            );
        self
            .nftContractDispatcher
            .write(
                IERC721Dispatcher {
                    contract_address: self.positionsDispatcher.read().get_nft_address()
                }
            );
    }

    #[abi(embed_v0)]
    impl EkuboLocker of super::IGrailsLocker<ContractState> {
        fn collectFees(ref self: ContractState, id: u64) -> (u128, u128) {
            let operator = self.operators.read(id);
            assert(get_caller_address() == operator, Errors::UNAUTHORIZED);

            let position = self.positions.read(id);
            let poolKey = position.poolKey;
            let bounds = position.bounds;

            let positionsDispatcher = self.positionsDispatcher.read();
            let tokenInfo = positionsDispatcher.get_token_info(id, poolKey, bounds);
            let fees0 = tokenInfo.fees0;
            let fees1 = tokenInfo.fees1;

            positionsDispatcher.collect_fees(id, poolKey, bounds);

            let token0Dispatcher = ERC20ABIDispatcher { contract_address: poolKey.token0 };
            token0Dispatcher.transfer(operator, fees0.into());
            let token1Dispatcher = ERC20ABIDispatcher { contract_address: poolKey.token1 };
            token1Dispatcher.transfer(operator, fees1.into());

            self.emit(CollectFees { id, fees0, fees1 });
            (fees0, fees1)
        }

        fn lock(
            ref self: ContractState,
            id: u64,
            unlockTimestamp: u64,
            poolKey: PoolKey,
            bounds: Bounds,
            operator: ContractAddress
        ) {
            self
                .nftContractDispatcher
                .read()
                .transfer_from(get_caller_address(), get_contract_address(), id.into());
            self.operators.write(id, operator);
            self.positions.write(id, Position { unlock: unlockTimestamp, poolKey: poolKey, bounds: bounds });
        }

        fn operator(self: @ContractState, id: u64) -> ContractAddress {
            self.operators.read(id)
        }

        fn positionsContract(self: @ContractState) -> ContractAddress {
            self.positionsDispatcher.read().contract_address
        }

        fn positionsNFTContract(self: @ContractState) -> ContractAddress {
            self.nftContractDispatcher.read().contract_address
        }

        fn transferOperator(ref self: ContractState, id: u64, newOperator: ContractAddress) {
            let operator = self.operators.read(id);
            assert(get_caller_address() == operator, Errors::UNAUTHORIZED);
            assert(newOperator.is_non_zero(), Errors::INVALID_OPERATOR);

            self.operators.write(id, newOperator);
            self.emit(TransferOperator { id, previousOperator: operator, newOperator });
        }

        fn unlock(ref self: ContractState, id: u64) {
            let operator = self.operators.read(id);
            assert(get_caller_address() == operator, Errors::UNAUTHORIZED);

            let mut position = self.positions.read(id);
            assert(position.unlock <= get_block_timestamp(), Errors::STILL_LOCKED);

            self.operators.write(id, 0x0.try_into().unwrap());
            position.unlock = 0;
            self.positions.write(id, position);
            self.nftContractDispatcher.read().transfer_from(get_contract_address(), operator, id.into());
        }
    }
}
