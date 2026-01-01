#!/usr/bin/env bash
set -euo pipefail

# a small helper that strips Coq “not found” and other warnings
filter_warnings() {
  grep -vE '^(Warning:|File |^\[)|redundant|ignoring it|module-not-found|has not been found|is required|let |'%_'|Code\ can\ be\ adapted|scope\ stack|printing'
}

# — disable *all* Coq warnings globally —
export COQFLAGS="-quiet -w none"
export COQDEPFLAGS="-quiet -w none"

# compute exactly what OPAM calls your local switch:
LOCAL_SWITCH="$(pwd)"

# 1) Create or reuse local opam switch
if ! opam switch list --short | grep -Fxq "$LOCAL_SWITCH"; then
  echo "Creating local switch at $LOCAL_SWITCH..."
  opam switch create . ocaml-variants.4.14.0+options ocaml-option-flambda --no-install
else
  echo "↻ Local switch already exists, skipping creation."
fi

# now load the switch into the env
eval "$(opam env)"

# 2. Add Coq repos
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev    https://gitlab.mpi-sws.org/iris/opam.git

# 3. Pin & install build deps
echo "🏗 Installing build dependencies from builddep/"
pushd builddep >/dev/null
  # drop any old pin, ignore errors
  opam pin remove templates-builddep -y 2>/dev/null || true
  # re-pin your .opam (picks up your corrected name/synopsis/%{make}%)
  opam pin add templates-builddep . --no-action -y
  # install only its dependencies
  opam install templates-builddep --deps-only -y
popd >/dev/null

# 4. Build VST
echo "🏗 Building VST"
pushd VST >/dev/null
  COQFLAGS="-quiet -w none" make -s 2>&1 | filter_warnings
popd >/dev/null

# 5. Build flows
echo "🏗 Building flows"
pushd flows >/dev/null
  make -s 2>/dev/null
  make -s install 2>/dev/null
popd >/dev/null

# 6. Build templates
echo "🏗 Building templates"
pushd templates >/dev/null
  make
popd >/dev/null

echo "✅ The artifact built successfully."
