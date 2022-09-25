FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh > elan-init.sh; \
  sh elan-init.sh -y; \
  python3 -m pip install --user pipx; \
  python3 -m pipx ensurepath; \
  /home/gitpod/.pyenv/shims/pipx install mathlibtools; \
  rm elan-init.sh;
