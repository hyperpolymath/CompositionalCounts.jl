# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# Never sourced. MGLM is called only through RCall from Julia, which renv's
# dependency scanner cannot see; this line declares it so `renv::status()` and
# `renv::snapshot()` agree with renv.lock.
library(MGLM)
