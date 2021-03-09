# Package not ready for stable.

build:
	# ... build ...
	cargo +nightly build
	# cargo +stable build
	# ... test ...
	cargo +nightly test --no-run
	# cargo +stable test --no-run
	# ... bench ...
	cargo +nightly bench --no-run
	# cargo +stable bench --no-run
	# ... bins ...
	cargo +nightly build --release --bin perf --features=perf
	# cargo +stable build --release --bin perf --features=perf
	# ... doc ...
	cargo +nightly doc
	# cargo +stable doc
	# ... meta commands ...
	cargo +nightly clippy --all-targets --all-features
prepare:
	check.sh
	perf.sh
clean:
	rm -f check.out perf.out
