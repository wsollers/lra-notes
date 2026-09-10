# ============================================================
# lra-notes - Lean 4 notes environment
# ============================================================
#
# Targets:
#   lean-build            Lean/Lake only, with dependencies preloaded
#
# The lean-build image is deliberately source-independent. It contains:
#   * OS tooling
#   * elan + the pinned Lean toolchain
#   * Lake dependency sources
#   * Mathlib's downloaded compiled cache
# ============================================================

FROM ubuntu:24.04 AS lean-build

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    make \
    bash \
    python3 \
    && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | bash -s -- -y --no-modify-path \
    && echo 'export PATH="$HOME/.elan/bin:$PATH"' >> /etc/environment

ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /workspace

COPY lean-toolchain ./lean-toolchain
RUN TOOLCHAIN="$(tr -d '\r\n' < lean-toolchain)" \
    && elan toolchain install "$TOOLCHAIN" \
    && elan default "$TOOLCHAIN"

# Use a dependency-only Lake file so ordinary edits to the real project
# lakefile.lean do not invalidate this expensive image layer.
COPY docker/lakefile.env.lean ./lakefile.lean
COPY lake-manifest.json ./lake-manifest.json

RUN lake update
RUN lake exe cache get

CMD ["bash"]
