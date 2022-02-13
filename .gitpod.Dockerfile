FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN brew install elan
RUN brew install leanproject
