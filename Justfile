checkout:
	cargo check
	cargo doc --features testing --document-private-items
	cargo build
	cargo build --example sieve
	cargo build --example tour
	cargo test --features testing
	cargo package --allow-dirty

dev:
	cargo check --features testing,serdes
	cargo test --features testing,serdes
	cargo doc --features testing,serdes --document-private-items

ci:
	watchexec -- just dev
