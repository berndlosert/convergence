FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN wget -q https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_debian.sh; \
  bash install_debian.sh; \
  rm -f install_debian.sh
