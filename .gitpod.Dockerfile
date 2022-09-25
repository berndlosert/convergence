FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh; \
  pipx install mathlibtools;
