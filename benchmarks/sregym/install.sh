#!/bin/bash

set -e

# Clone submodule to SREGym-applications if no file in sregym_core/SREGym-applications
if [ ! -f "sregym_core/SREGym-applications/README.md" ]; then
    echo "==> Cloning SREGym-applications..."
    git clone https://github.com/SREGym/SREGym-applications.git sregym_core/SREGym-applications --recurse-submodules
else
    echo "==> SREGym-applications already exists. Skipping clone."
fi

# Homebrew installation
if ! command -v brew >/dev/null 2>&1; then
    echo "==> Homebrew not found. Installing Homebrew..."
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
fi

# Helm installation
if ! command -v helm >/dev/null 2>&1; then
    echo "==> Helm not found. Installing Helm..."
    brew install helm
fi

# Detect architecture and set kubectl architecture
ARCH=$(uname -m)
if [ "$ARCH" == "x86_64" ]; then
    KUBECTL_ARCH="amd64"
    echo "==> x86_64 machine detected. Using amd64 kubectl."
elif [ "$ARCH" == "aarch64" ]; then
    KUBECTL_ARCH="arm64"
    echo "==> aarch64 machine detected. Using arm64 kubectl."
else
    echo "==> Unknown machine type detected: $ARCH"
    exit 1
fi

# kubectl installation
if ! command -v kubectl >/dev/null 2>&1; then
    echo "==> kubectl not found. Installing kubectl..."
    
    # Get the latest stable version
    KUBECTL_VERSION=$(curl -L -s https://dl.k8s.io/release/stable.txt)
    echo "==> Installing kubectl version: $KUBECTL_VERSION"
    
    # Download kubectl binary
    curl -LO "https://dl.k8s.io/release/${KUBECTL_VERSION}/bin/linux/${KUBECTL_ARCH}/kubectl"
    
    # Download kubectl checksum file
    curl -LO "https://dl.k8s.io/release/${KUBECTL_VERSION}/bin/linux/${KUBECTL_ARCH}/kubectl.sha256"
    
    # Validate the binary against the checksum file
    echo "$(cat kubectl.sha256)  kubectl" | sha256sum --check
    if [ $? -ne 0 ]; then
        echo "==> Error: kubectl checksum validation failed!"
        rm -f kubectl kubectl.sha256
        exit 1
    fi
    
    # Install kubectl
    sudo install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl
    
    # Clean up installation files
    rm -f kubectl kubectl.sha256
    
    # Verify installation
    kubectl version --client
    echo "==> kubectl installed successfully."
else
    echo "==> kubectl is already installed."
    kubectl version --client
fi

# Install uv (Python package manager)
if ! command -v uv >/dev/null 2>&1; then
    echo "==> uv not found. Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    
    # Add uv to PATH if not already there
    export PATH="$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
    
    # Verify installation
    if command -v uv >/dev/null 2>&1; then
        uv --version
        echo "==> uv installed successfully."
    else
        echo "==> Warning: uv installation may have failed. Please check your PATH."
        echo "==> You may need to add ~/.cargo/bin or ~/.local/bin to your PATH."
    fi
else
    echo "==> uv is already installed."
    uv --version
fi

# Synchronize the dependencies
cd sregym_core
uv sync
uv run pre-commit install

# Check for inventory.yml and configure remote cluster if present
if [ -f "scripts/ansible/inventory.yml" ]; then
    echo "==> Found inventory.yml. Checking if cluster already exists..."
    
    # Check if cluster is already configured
    CLUSTER_EXISTS=false
    if kubectl get nodes >/dev/null 2>&1; then
        READY_NODES=$(kubectl get nodes --no-headers 2>/dev/null | grep -c " Ready " || true)
        TOTAL_NODES=$(kubectl get nodes --no-headers 2>/dev/null | wc -l || true)
        
        if [ "$TOTAL_NODES" -gt 0 ] && [ "$READY_NODES" -eq "$TOTAL_NODES" ]; then
            CLUSTER_EXISTS=true
            echo "==> Cluster already exists with $TOTAL_NODES node(s) in Ready state."
            echo "==> Cluster nodes:"
            kubectl get nodes
            echo ""
            echo "==> ✓ Skipping cluster setup. Cluster is already configured correctly."
        fi
    fi
    
    # Only run ansible-playbook if cluster doesn't exist or is not fully ready
    if [ "$CLUSTER_EXISTS" = false ]; then
        echo "==> Cluster not found or not fully ready. Configuring remote cluster with Ansible..."
        cd scripts/ansible
        ansible-playbook -i inventory.yml setup_cluster.yml
        
        if [ $? -eq 0 ]; then
            echo "==> Ansible playbook completed successfully."
            
            # Verify cluster configuration with kubectl
            echo "==> Verifying cluster configuration..."
            if kubectl get nodes >/dev/null 2>&1; then
                echo "==> Cluster nodes:"
                kubectl get nodes
                echo ""
                
                # Check if nodes are in Ready state
                READY_NODES=$(kubectl get nodes --no-headers 2>/dev/null | grep -c " Ready " || true)
                TOTAL_NODES=$(kubectl get nodes --no-headers 2>/dev/null | wc -l || true)
                
                if [ "$READY_NODES" -gt 0 ] && [ "$READY_NODES" -eq "$TOTAL_NODES" ]; then
                    echo "==> ✓ All nodes are in Ready state. Cluster configuration is correct."
                elif [ "$READY_NODES" -gt 0 ]; then
                    echo "==> ⚠ Warning: Only $READY_NODES out of $TOTAL_NODES nodes are Ready."
                    echo "==> Please check the cluster status manually."
                else
                    echo "==> ⚠ Warning: No nodes are in Ready state."
                    echo "==> Please check the cluster status manually."
                fi
else
                echo "==> ⚠ Warning: kubectl cannot connect to the cluster."
                echo "==> Please verify the cluster configuration manually."
            fi
            cd - >/dev/null
        else
            echo "==> Error: Ansible playbook failed."
            cd - >/dev/null
            exit 1
        fi
    fi
else
    echo "==> No inventory.yml found at scripts/ansible/inventory.yml. Skipping remote cluster setup."
    echo "==> To set up a remote cluster, create inventory.yml from inventory.yml.example"
fi

cd -

source sregym_core/.venv/bin/activate
# uv pip install -r requirements.txt
deactivate
