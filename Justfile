checkout:
	cargo check
	cargo doc --document-private-items --features testing
	cargo build
	cargo build --example sieve
	cargo build --example tour
	cargo test --features testing
	cargo package --allow-dirty

dev:
	cargo check
	cargo test --features testing
	cargo doc --document-private-items --features testing
