COVERAGE=cargo llvm-cov --doctests
coverage:
	@$(COVERAGE) | bat --wrap=never

coverage-html:
	@$(COVERAGE) --open

coverage-diff:
	@$(COVERAGE) --text --color=always

.PHONY: web web-serve gui gui-web gui-web-serve
web:
	wasm-pack build crates/formalith-web --target web --release --out-dir www/pkg --no-typescript

web-serve: web
	python -m http.server -d crates/formalith-web/www 8000

gui:
	cargo run -p formalith-gui --release

gui-web:
	wasm-pack build crates/formalith-gui --target web --release --out-dir www/pkg --no-typescript

gui-web-serve: gui-web
	python -m http.server -d crates/formalith-gui/www 8001
