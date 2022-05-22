# Package not ready for stable.

build:
	# ... build ...
	cargo +stable build
	cargo +nightly build
	#
	# ... test ...
	cargo +stable test --no-run
	cargo +nightly test --no-run
	#
	# ... bench ...
	cargo +nightly bench --no-run
	#
	# ... doc ...
	cargo +stable doc
	cargo +nightly doc
	#
	# ... bins ...
	cargo +stable build --release --bin perf --features=perf
	cargo +nightly build --release --bin perf --features=perf
	#
	# ... meta commands ...
	cargo +nightly clippy --all-targets --all-features

test:
	# ... test ...
	cargo +stable test
	cargo +nightly test

bench:
	# ... bench ...
	cargo +stable bench
	cargo +nightly bench

flamegraph:
	cargo flamegraph --features=perf --release --bin=perf -- --load 1000000 --ops 10000

prepare: build test bench
	check.sh check.out
	perf.sh perf.out

clean:
	cargo clean
	rm -f check.out perf.out flamegraph.svg perf.data perf.data.old core
