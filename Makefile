# Package not ready for stable.

build:
	# ... build ...
	cargo +nightly build
	# ... test ...
	cargo +nightly test --no-run
	# ... bench ...
	cargo +nightly bench --no-run
	# ... doc ...
	cargo +nightly doc
	# ... bins ...
	cargo +nightly build --release --bin perf --features=perf
	# ... meta commands ...
	cargo +nightly clippy --all-targets --all-features
flamegraph:
	cargo flamegraph --features=perf --release --bin=perf -- --load 1000000 --ops 10000
prepare:
	check.sh
	perf.sh
clean:
	rm -f check.out perf.out
