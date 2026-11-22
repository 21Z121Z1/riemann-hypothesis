import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentatives

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleTransportRep
section
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

section Generators

variable (K : Type) [Field K] [Fintype K]

theorem exists_root_over {F : Type} [Field F] {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) {z w : F}
    (hz : IsPrimitiveRoot z N) (hw : IsPrimitiveRoot w M) : ∃ z' : F, IsPrimitiveRoot z' M ∧ z' ^ (M / N) = z := by
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNM hM
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  have hw' : IsPrimitiveRoot (w ^ (M / N)) N := hw.pow hM (Nat.div_mul_cancel hNM).symm
  obtain ⟨a, -, ha, hza⟩ := (hw'.isPrimitiveRoot_iff).1 hz
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfCoprime a ha)
  have h1 : ((u : ZMod M).val : ZMod N) = (a : ZMod N) := by
    have := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
    simpa [ZMod.unitsMap_val] using this
  refine ⟨w ^ (u : ZMod M).val, hw.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← hza]
  exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1) hw'.pow_eq_one

theorem lev_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' Fintype.one_lt_card)

theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ w : AlgebraicClosure K, IsPrimitiveRoot w (Fintype.card K ^ d - 1) := by
  have h1 : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
  have hq : ((Fintype.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.cast_card_eq_zero, map_zero]
  haveI : NeZero ((Fintype.card K ^ d - 1 : ℕ) : AlgebraicClosure K) := ⟨by
    rw [Nat.cast_sub h1, Nat.cast_pow, hq, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨(lev_pos K hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

noncomputable def tower : (k : ℕ) → {z : AlgebraicClosure K // IsPrimitiveRoot z (Fintype.card K ^ k.factorial - 1)}
  | 0 => ⟨(exists_prim K (Nat.factorial_pos 0)).choose, (exists_prim K (Nat.factorial_pos 0)).choose_spec⟩
  | k + 1 =>
    have h := exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec
    ⟨h.choose, h.choose_spec.1⟩

theorem tower_succ (k : ℕ) :
    (tower K (k + 1)).1 ^ ((Fintype.card K ^ (k + 1).factorial - 1) / (Fintype.card K ^ k.factorial - 1)) =
      (tower K k).1 :=
  (exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower K k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec).choose_spec.2

theorem tower_le {k l : ℕ} (h : k ≤ l) :
    (tower K l).1 ^ ((Fintype.card K ^ l.factorial - 1) / (Fintype.card K ^ k.factorial - 1)) = (tower K k).1 := by
  induction l, h using Nat.le_induction with
  | base => rw [Nat.div_self (lev_pos K (Nat.factorial_pos k)), pow_one]
  | succ l hl ih =>
    rw [← Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ l)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hl)), pow_mul, tower_succ, ih]

theorem exists_genSys : ∃ ζ : ℕ → AlgebraicClosure K, ∀ d, 0 < d → orderOf (ζ d) = Fintype.card K ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((Fintype.card K ^ d' - 1) / (Fintype.card K ^ d - 1)) = ζ d := by
  refine ⟨fun d => (tower K d).1 ^ ((Fintype.card K ^ d.factorial - 1) / (Fintype.card K ^ d - 1)),
    fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · have hdv := Nat.pow_sub_one_dvd_pow_sub_one (Fintype.card K) (Nat.dvd_factorial hd le_rfl)
    exact ((tower K d).2.pow (lev_pos K (Nat.factorial_pos d)) (Nat.div_mul_cancel hdv).symm).eq_orderOf.symm
  · have hle : d ≤ d' := Nat.le_of_dvd hd' hdd
    show ((tower K d').1 ^ _) ^ _ = (tower K d).1 ^ _
    rw [← pow_mul, Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd' le_rfl))
      (Nat.pow_sub_one_dvd_pow_sub_one _ hdd), ← tower_le K hle, ← pow_mul,
      Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hle))
        (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd le_rfl))]

theorem nonempty_labelConv [DecidableEq K] : Nonempty (Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.CuspGL.TeichEmb.exists_teichmuller K
  obtain ⟨ζ, hζ⟩ := exists_genSys K
  exact ⟨{ ι := θ, ι_inj := hθ, gen := ζ, gen_order := fun d hd => (hζ d hd).1
           gen_norm := fun d e hd he => (hζ d hd).2 (d * e) (Dvd.intro _ rfl) (Nat.mul_pos hd he) }⟩

theorem exists_monic_irreducible (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : NeZero d := ⟨by omega⟩
  let E := FiniteField.Extension K (ringChar K) d
  have hfin : Module.finrank K E = d := FiniteField.finrank_extension K (ringChar K) d
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ IntermediateField.adjoin K {α} = ⊤ := by
    by_cases h : β = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      subst h
      rw [IntermediateField.adjoin_one]
      rwa [IntermediateField.adjoin_zero] at hβ
    · exact ⟨β, h, hβ⟩
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly K α, minpoly.monic hint, minpoly.irreducible hint, fun h => hα0 ?_, ?_⟩
  · have h0 := minpoly.aeval K α
    rwa [h, aeval_X] at h0
  · rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', hfin]

end Generators

section Transport

variable {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def transportRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem transportRep_apply (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

end Transport

theorem isIrreducible_transportRep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) : (transportRep ρ e).IsIrreducible := by
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨e.symm.toEquiv.nontrivial, fun U hU => ?_⟩
  have hinv : ∀ g, ∀ v ∈ U.comap e.toLinearMap, ρ g v ∈ U.comap e.toLinearMap := by
    intro g v hv
    have h1 := hU g (e v) hv
    rw [transportRep_apply, e.symm_apply_apply] at h1
    exact h1
  rcases h _ hinv with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by
      show e (e.symm w) ∈ U
      rwa [e.apply_symm_apply]
    rw [h0, Submodule.mem_bot] at h1
    simpa using h1
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by rw [h0]; trivial
    have h2 : e (e.symm w) ∈ U := h1
    rwa [e.apply_symm_apply] at h2

theorem isCuspidal_transportRep {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : FDRep ℂ (GL (Fin N) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) (e : τ ≃ₗ[ℂ] W) :
    GlobalTheory.FiniteGL.IsCuspidal (transportRep τ.ρ e) := by
  rw [GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks]
  intro a ha haN w hw
  let b : Fin N → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  have hs : Function.Surjective b := by
    intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [b, ha]⟩
    · exact ⟨⟨a, haN⟩, by simp [b]⟩
  have h0 := h 2 b hs le_rfl (e.symm w) (fun u hu => ?_)
  · simpa using h0
  · obtain ⟨⟨hUT, -⟩, hdiag⟩ := hu
    have hu' : u ∈ GlobalTheory.FiniteGL.unipRadical K (GlobalTheory.FiniteGL.twoBlocks N a) := by
      intro i j hij
      have hlt : b i = b j ∨ b j < b i := by
        simp only [b, GlobalTheory.FiniteGL.twoBlocks] at hij ⊢
        split_ifs at hij ⊢ <;> simp_all
      rcases hlt with hb | hb
      · rw [Matrix.sub_apply, hdiag i j hb, Matrix.one_apply, sub_self]
      · have hne : i ≠ j := fun e' => by rw [e'] at hb; exact lt_irrefl _ hb
        rw [Matrix.sub_apply, hUT i j hb, Matrix.one_apply_ne hne, sub_zero]
    have h1 := hw u hu'
    rw [transportRep_apply] at h1
    apply e.injective
    rw [h1, e.apply_symm_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

theorem GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds : GlobalTheory.Published.CuspidalExists := by
  intro k _ _ n
  classical
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv k
  obtain ⟨P, h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible k (n + 1) (by omega)
  obtain ⟨τ, hs, hc, -⟩ := GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label k C (n + 1) (by omega) P h1 h2 h3 h4
  have hI := (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 _ τ).1 hs
  let e := (Module.finBasis ℂ τ).equivFun
  exact ⟨_, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.transportRep τ.ρ e,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isIrreducible_transportRep τ.ρ e hI.1 hI.2,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isCuspidal_transportRep τ hc e⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaPrimeTwistSummableStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_prime_twist_summable : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)), (Ideal.absNorm 𝔠).Prime →
  ∀ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}, (∀ J, (e J).1 = 𝔠 * J.1) →
  ∀ (s : ℂ) (t : ℂ), 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t →
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummableStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_ray_class_summable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifferenceStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_twisted_entire_difference : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd

theorem periodic_mul {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (i : Fin r) (k : ℕ)
    (m : Fin r → ℕ) : v (m + (Pi.single i (k * l) : Fin r → ℕ)) = v m := by
  induction k with
  | zero => simp
  | succ k ih => rw [add_mul, one_mul, Pi.single_add, ← add_assoc, hv, ih]

theorem reduce_on {r l : ℕ} {v : (Fin r → ℕ) → ℚ}
    (hv : ∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) (s : Finset (Fin r))
    (m : Fin r → ℕ) : v m = v (fun i => if i ∈ s then m i % l else m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [ih]
    have hfun : (fun i => if i ∈ s then m i % l else m i) =
        (fun i => if i ∈ insert a s then m i % l else m i) +
          (Pi.single a (m a / l * l) : Fin r → ℕ) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha, Nat.mod_add_div']
      · simp [hj, Pi.single_eq_of_ne hj]
    rw [hfun, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.periodic_mul hv]

theorem bddW_of_periodic : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l →
    (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  intro r l v hl hv
  refine ⟨∑ f : Fin r → Fin l, |((v fun i => (f i : ℕ) : ℚ) : ℝ)|, fun m => ?_⟩
  have hm : v m = v fun i => ((⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l) : ℕ) := by
    simpa using GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.reduce_on hv Finset.univ m
  rw [hm]
  exact Finset.single_le_sum (f := fun f : Fin r → Fin l => |((v fun i => (f i : ℕ) : ℚ) : ℝ)|)
    (fun f _ => abs_nonneg _) (Finset.mem_univ fun i => (⟨m i % l, Nat.mod_lt _ hl⟩ : Fin l))

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrizationStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_cone_parametrization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassGroupFiniteRepresentativesStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_group_finite_representatives : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
    ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassPrimeMultiplicationPermutationStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_prime_multiplication_permutation : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))), 𝔣 ≠ ⊥ → 𝔠.IsPrime → 𝔠 ≠ ⊥ → 𝔠 ⊔ 𝔣 = ⊤ →
  (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) → (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) →
  ∃ τ : Equiv.Perm S, ∀ c : S,
    ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
        {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
      ∀ J, (e J).1 = 𝔠 * J.1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RealDifferenceConeBound
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue

theorem entire_of_halfPlane_continuations :
    ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  intro S G hG hS
  have hopen : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re} := fun r =>
    isOpen_lt continuous_const Complex.continuous_re

  have hagree : ∀ j k : ℕ, j ≤ k → Set.EqOn (G j) (G k) {s : ℂ | -(j : ℝ) < s.re} := by
    intro j k hjk
    have hsub : {s : ℂ | -(j : ℝ) < s.re} ⊆ {s : ℂ | -(k : ℝ) < s.re} := by
      intro s hs
      have h1 : (j : ℝ) ≤ k := by exact_mod_cast hjk
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith
    have hfj : AnalyticOnNhd ℂ (G j) {s : ℂ | -(j : ℝ) < s.re} :=
      (hG j).analyticOnNhd (hopen _)
    have hfk : AnalyticOnNhd ℂ (G k) {s : ℂ | -(j : ℝ) < s.re} :=
      ((hG k).mono hsub).analyticOnNhd (hopen _)
    have hpre : IsPreconnected {s : ℂ | -(j : ℝ) < s.re} :=
      (convex_halfSpace_re_gt (-(j : ℝ))).isPreconnected
    have h2 : (2 : ℂ) ∈ {s : ℂ | -(j : ℝ) < s.re} := by
      have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]
      linarith
    have hev : G j =ᶠ[nhds (2 : ℂ)] G k := by
      have hmem : {s : ℂ | (1 : ℝ) < s.re} ∈ nhds (2 : ℂ) :=
        (hopen 1).mem_nhds (by simp)
      filter_upwards [hmem] with s hs
      rw [hS j s hs, hS k s hs]
    exact hfj.eqOn_of_preconnected_of_eventuallyEq hfk hpre h2 hev

  have hidx : ∀ s : ℂ, -((⌈-s.re⌉₊ + 1 : ℕ) : ℝ) < s.re := by
    intro s
    have h1 : -s.re ≤ (⌈-s.re⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith

  have hT : ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → G (⌈-s.re⌉₊ + 1) s = G k s := by
    intro k s hs
    rcases le_total (⌈-s.re⌉₊ + 1) k with h | h
    · exact hagree _ _ h (hidx s)
    · exact (hagree _ _ h hs).symm
  refine ⟨fun s => G (⌈-s.re⌉₊ + 1) s, ?_, hT⟩
  intro s
  set k := ⌈-s.re⌉₊ + 1 with hk
  have hs : s ∈ {w : ℂ | -(k : ℝ) < w.re} := hidx s
  have hnh : {w : ℂ | -(k : ℝ) < w.re} ∈ nhds s := (hopen _).mem_nhds hs
  have hd : DifferentiableAt ℂ (G k) s := (hG k).differentiableAt hnh
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnh] with w hw
  exact hT k w hw

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecomposition
section
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem sum_equivFin_symm {F M : Type} [AddCommMonoid M] (s : Finset F) (f : F → M) :
    ∑ i : Fin s.card, f (s.equivFin.symm i : F) = ∑ y ∈ s, f y := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun y : s => f (y : F))

theorem openCone_equivFin {F : Type} [Field F] [CharZero F] (s : Finset F) :
    openCone (fun i : Fin s.card => (s.equivFin.symm i : F)) = coneOn s := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun y => if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1, ?_, ?_⟩
    · intro y hy
      simp only [dif_pos hy]
      exact ht _
    · rw [← sum_equivFin_symm s (fun y => (if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1 : ℚ) • y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm : (s.equivFin.symm i : F) ∈ s := (s.equivFin.symm i).2
      simp only [dif_pos hm, Subtype.coe_eta, Equiv.apply_symm_apply]
      rw [Rat.smul_def]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t (s.equivFin.symm i : F), fun i => ht _ (s.equivFin.symm i).2, ?_⟩
    rw [← sum_equivFin_symm s (fun y => t y • y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def]

theorem tile_family {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F) (h : Tile P Q C) :
    (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  induction h with
  | empty =>
    intro _
    exact ⟨Empty, inferInstance, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim,
      fun c => c.elim, fun c => c.elim, fun x hx => hx.elim⟩
  | cone s hli hP hQ =>
    intro h0
    have hcone := openCone_equivFin s
    refine ⟨Unit, inferInstance, fun _ => s.card, fun _ i => (s.equivFin.symm i : F), ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
      rintro rfl
      exact h0 ⟨fun _ => 0, by simp, by simp⟩
    · intro _
      have hinj : Function.Injective (fun i : Fin s.card => (⟨(s.equivFin.symm i : F), (s.equivFin.symm i).2⟩ : (s : Set F))) := by
        intro i j hij
        exact s.equivFin.symm.injective (Subtype.ext (congrArg Subtype.val hij))
      exact LinearIndependent.comp hli _ hinj
    · intro _ i
      exact hP (s.equivFin.symm i).2
    · intro _
      exact hcone.le
    · intro x hx
      exact ⟨(), hcone.ge hx, fun _ _ => rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    intro h0
    obtain ⟨ι₁, f₁, r₁, v₁, hr₁, hl₁, hp₁, hs₁, hu₁⟩ := ihA (fun h => h0 (Or.inl h))
    obtain ⟨ι₂, f₂, r₂, v₂, hr₂, hl₂, hp₂, hs₂, hu₂⟩ := ihB (fun h => h0 (Or.inr h))
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim r₁ r₂,
      fun c => match c with
        | Sum.inl a => v₁ a
        | Sum.inr b => v₂ b, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      · exact hr₁ a
      · exact hr₂ b
    · rintro (a | b)
      · exact hl₁ a
      · exact hl₂ b
    · rintro (a | b) i
      · exact hp₁ a i
      · exact hp₂ b i
    · rintro (a | b)
      · exact (hs₁ a).trans Set.subset_union_left
      · exact (hs₂ b).trans Set.subset_union_right
    · rintro x (hx | hx)
      · obtain ⟨a, ha, hu⟩ := hu₁ x hx
        refine ⟨Sum.inl a, ha, ?_⟩
        rintro (a' | b') h'
        · exact congrArg Sum.inl (hu a' h')
        · exact (Set.disjoint_left.mp hAB hx (hs₂ b' h')).elim
      · obtain ⟨b, hb, hu⟩ := hu₂ x hx
        refine ⟨Sum.inr b, hb, ?_⟩
        rintro (a' | b') h'
        · exact (Set.disjoint_left.mp hAB (hs₁ a' h') hx).elim
        · exact congrArg Sum.inr (hu b' h')

theorem tile_family_closed : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) :=
  fun P Q C h => tile_family P Q C h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

