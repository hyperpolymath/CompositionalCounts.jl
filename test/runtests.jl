# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

using CompositionalCounts
using Test

@testset "CompositionalCounts" begin
    @testset "validate_counts" begin
        Y = [3 0 5; 1 2 0; 0 4 4]
        @test validate_counts(Y) === nothing
        @test_throws InvalidCounts validate_counts([1 -1; 2 2])
        @test_throws InvalidCounts validate_counts([1.5 1; 2 2])
        @test_throws InvalidCounts validate_counts([1 NaN; 2 2])
        @test_throws InvalidCounts validate_counts([0 0; 2 2])        # empty sample
        @test_throws InvalidCounts validate_counts(reshape([1, 2], 2, 1))  # J = 1
        @test_throws UnidentifiableTaxon validate_counts([1 0; 2 0])
    end

    @testset "validate_design" begin
        X = [1 0.0; 1 1.0; 1 2.0]
        @test validate_design(X, 3) === nothing
        @test_throws RankDeficientDesign validate_design([1 2.0; 1 2.0; 1 2.0], 3)
        @test_throws RankDeficientDesign validate_design(X, 4)
        @test_throws RankDeficientDesign validate_design([1 0.0 1.0; 1 1.0 2.0], 2)  # n ≤ p
    end

    @testset "reference taxon (rule 4)" begin
        # taxon 1: prevalence 1.0, total 6; taxon 2: prevalence 2/3, total 6;
        # taxon 3: prevalence 1/3, total 9
        Y = [3 0 9; 1 2 0; 2 4 0]
        @test prevalence(Y, 1) == 1.0
        @test select_reference(Y) == 1
        @test validate_reference(Y, 2) == 2
        @test_throws InvalidReference validate_reference(Y, 3)   # refused, never replaced
        @test_throws InvalidReference validate_reference(Y, 4)
        # tie on prevalence → larger total wins; tie on both → lower index
        @test select_reference([1 5; 1 5]) == 2
        @test select_reference([2 2; 2 2]) == 1
        # positive control: no admissible reference at all
        @test_throws InvalidReference select_reference([1 0 0; 0 1 0; 0 0 1])   # every prevalence 1/3
    end
end
