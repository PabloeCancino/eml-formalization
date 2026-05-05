#!/usr/bin/env bash
set -e

echo "==> Instalando elan (Lean version manager)..."
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi

# Agregar elan al PATH de forma idempotente
grep -qxF 'export PATH="$HOME/.elan/bin:$PATH"' "$HOME/.bashrc" \
  || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"

export PATH="$HOME/.elan/bin:$PATH"

echo "==> Verificando versiones..."
elan --version
lean --version
lake --version

echo "==> Ejecutando lake update en ./lean4..."
if [ -f "./lean4/lakefile.toml" ] || [ -f "./lean4/lakefile.lean" ]; then
  cd lean4
  lake update
  echo "==> lake update completado."
else
  echo "WARN: No se encontró lakefile en ./lean4"
fi
