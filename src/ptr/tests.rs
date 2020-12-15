#![cfg(test)]

use crate::{
	mutability::Const,
	order::Lsb0,
	ptr::BitPtr,
};

use static_assertions::assert_not_impl_any;

#[test]
fn pointers_not_send_sync() {
	assert_not_impl_any!(BitPtr<Const, Lsb0, u8>: Send, Sync);
}
