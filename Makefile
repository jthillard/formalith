COVERAGE=cargo llvm-cov --doctests
coverage:
	@$(COVERAGE) | bat --wrap=never

coverage-html:
	@$(COVERAGE) --open

coverage-diff:
	@$(COVERAGE) --text --color=always

.PHONY: web web-serve gui gui-web gui-web-serve gui-profile gui-web-profile
web:
	wasm-pack build crates/formalith-web --target web --profile wasm-release --out-dir www/pkg --no-typescript

web-serve: web
	python -m http.server -d crates/formalith-web/www 8000

gui:
	cargo run -p formalith-gui --release

# The interface and its Web Worker evaluating the lines, as two wasm modules
gui-web:
	wasm-pack build crates/formalith-gui --target web --profile wasm-release --out-dir www/pkg --no-typescript
	wasm-pack build crates/formalith-gui-worker --target web --profile wasm-release --out-dir ../formalith-gui/www/worker-pkg --no-typescript

gui-web-serve: gui-web
	python -m http.server -d crates/formalith-gui/www 8001

# With the profiler window (F12)
gui-profile:
	cargo run -p formalith-gui --release --features profile

gui-web-profile:
	wasm-pack build crates/formalith-gui --target web --profile wasm-release --out-dir www/pkg --no-typescript -- --features profile
	wasm-pack build crates/formalith-gui-worker --target web --profile wasm-release --out-dir ../formalith-gui/www/worker-pkg --no-typescript -- --features profile
	python -m http.server -d crates/formalith-gui/www 8001
