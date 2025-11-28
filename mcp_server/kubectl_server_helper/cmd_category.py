kubectl_safe_commands = [
    "kubectl annotate",
    "kubectl api-resources",
    "kubectl api-version",
    "kubectl attach",
    "kubectl auth",
    "kubectl cluster-info",
    "kubectl completion",
    "kubectl describe",
    "kubectl diff",
    "kubectl drain",
    "kubectl events",
    "kubectl explain",
    "kubectl expose",
    "kubectl get",
    "kubectl logs",
    "kubectl options",
    "kubectl top",
    "kubectl version",
]

kubectl_unsafe_commands = [
    "kubectl apply",
    "kubectl autoscale",
    "kubectl certificate",
    "kubectl config",
    "kubectl cordon",
    "kubectl cp",
    "kubectl create",
    "kubectl delete",
    # exec likely needs special consideration, since it *could* be interactive if they did exec /bin/bash
    "kubectl exec",
    "kubectl kustomize",
    "kubectl label",
    "kubectl patch",
    "kubectl plugins",
    "kubectl port-forward",
    "kubectl proxy",
    "kubectl replace",
    "kubectl rollout",
    "kubectl run",
    "kubectl scale",
    "kubectl set",
    "kubectl uncordon",
    "kubectl taint",
]

# Interactive commands like edit and debug don't work with our agent
kubectl_unsupported_commands = [
    "kubectl debug",
    "kubectl edit",
    "kubectl wait",
    "kubectl proxy",  # This will keep running
    "kubectl port-forward",  # This will keep running
    "kubectl cp",  # Should not support file based operations
]

# Commands that support dry-run
kubectl_dry_run_commands = [
    "kubectl annotate",
    "kubectl drain",
    "kubectl expose",
    "kubectl apply",
    "kubectl autoscale",
    "kubectl cordon",
    "kubectl create",
    "kubectl delete",
    "kubectl label",
    "kubectl patch",
    "kubectl replace",
    "kubectl run",
    "kubectl scale",
    "kubectl set",
    "kubectl rollout undo",
    "kubectl uncordon",
    "kubectl taint",
    "kubectl auth reconcile",
]
