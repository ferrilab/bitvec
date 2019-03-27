checkout:
	cargo check
	cargo clippy --features serdes,testing
	cargo doc --features serdes,testing --document-private-items
	cargo build
	cargo build --example sieve
	cargo build --example tour
	cargo build --example serdes --features serdes
	cargo test --features serdes,testing
	cargo package --allow-dirty

dev:
	cargo check --features serdes,testing
	cargo clippy --features serdes,testing
	cargo test --features serdes,testing
	cargo doc --features serdes,testing --document-private-items

ci:
	watchexec -- just dev

publish: checkout
	cargo publish
