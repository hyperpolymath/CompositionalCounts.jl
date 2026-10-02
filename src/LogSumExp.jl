# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

"""
    logsumexp(v)

Numerically stable `log(sum(exp.(v)))`, computed by shifting by `maximum(v)`;
softmax shift invariance (proved in `proofs/`) is what makes the shift exact.
"""
function logsumexp(v::AbstractVector{<:Real})
    m = maximum(v)
    isfinite(m) || return m
    s = zero(float(m))
    @inbounds for x in v
        s += exp(x - m)
    end
    return m + log(s)
end

"""
    softmax!(p, v)

Write the softmax of `v` into `p` using the max-shift, and return `p`.
"""
function softmax!(p::AbstractVector, v::AbstractVector{<:Real})
    m = maximum(v)
    @inbounds for j in eachindex(v)
        p[j] = exp(v[j] - m)
    end
    p ./= sum(p)
    return p
end
