import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ZLat

open GlobalTheory.SW.TensLat GlobalTheory.SW.TensVac

theorem exists_even_reps {G : Type} [AddCommGroup G] (A C : AddSubgroup G) {M : ℕ} (hM : Odd M)
    (hA : ∀ a ∈ A, M • a ∈ C) {c : ℕ} (hc : C.relIndex A = c) (h0 : c ≠ 0) :
    ∃ a : Fin c → G, (∀ i, a i ∈ A) ∧ (∀ i i', 2 • a i - 2 • a i' ∈ C → i = i') ∧
      ∀ y ∈ A, ∃ i, y - 2 • a i ∈ C := by
  obtain ⟨k, rfl⟩ := hM
  have hcard : Nat.card (A ⧸ C.addSubgroupOf A) = c := hc
  haveI : Finite (A ⧸ C.addSubgroupOf A) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  let e := (Finite.equivFinOfCardEq hcard).symm
  have key (x : A) : 2 • ((k + 1) • (x : G)) = x + (2 * k + 1) • (x : G) := by
    rw [smul_smul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, succ_nsmul, add_comm]
  refine ⟨fun i => (k + 1) • ((e i).out : A), fun i => A.nsmul_mem (e i).out.2 _, ?_, ?_⟩
  · intro i i' h
    apply e.injective
    rw [← QuotientAddGroup.out_eq' (e i), ← QuotientAddGroup.out_eq' (e i'), eq_comm,
      QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [key, key] at h
    have := C.add_mem (C.sub_mem h (hA _ (e i).out.2)) (hA _ (e i').out.2)
    convert this using 1
    push_cast
    abel
  · intro y hy
    refine ⟨e.symm (⟨y, hy⟩ : A), ?_⟩
    rw [key, Equiv.apply_symm_apply]
    have h := QuotientAddGroup.out_eq' ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have := C.sub_mem h (hA _ ((⟨y, hy⟩ : A) : A ⧸ C.addSubgroupOf A).out.2)
    convert this using 1
    push_cast
    abel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

omit [IsCMField E] in
theorem stdLat_eq : stdLat E n = stdL E n := by
  ext x
  rw [Base.mem_stdL, stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [IsCMField E] in
theorem mem_span_smul {N : ℕ} {S : Lt E n} {v : Fin n → E} :
    v ∈ Ideal.span {(N : 𝓞 E)} • S ↔ ∃ v' ∈ S, N • v' = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Nat.cast_smul_eq_nsmul]

omit [IsCMField E] in
theorem vecMulVec_nsmul (N : ℕ) (v : Fin n → E) (u : Fin r → E) :
    vecMulVec (N • v) u = N • vecMulVec v u := by
  ext i j
  simp [vecMulVec_apply, _root_.mul_assoc]

omit [IsCMField E] in
theorem mem_tens_span_smul {N : ℕ} {S : Lt E n} {L : Lt E r} {y : Matrix (Fin n) (Fin r) E} :
    y ∈ tens (Ideal.span {(N : 𝓞 E)} • S) L ↔ ∃ z ∈ tens S L, N • z = y := by
  have : tens (Ideal.span {(N : 𝓞 E)} • S) L = (tens S L).map (nsmulAddMonoidHom N) := by
    apply le_antisymm
    · refine tens_le fun v hv u hu => ?_
      obtain ⟨v', hv', rfl⟩ := mem_span_smul.1 hv
      exact ⟨_, pure_mem hv' hu, (vecMulVec_nsmul N v' u).symm⟩
    · rw [AddSubgroup.map_le_iff_le_comap]
      refine tens_le fun v hv u hu => ?_
      rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
      exact pure_mem (mem_span_smul.2 ⟨v, hv, rfl⟩) hu
  rw [this]
  rfl

theorem nsmul_mem_std {N : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n 1)
    (h : Ideal.span {(N : 𝓞 E)} • stdL E n ≤ Λ) {v : Fin n → E} (hv : v ∈ Λ) :
    N • v ∈ stdL E n := by
  rw [(Base.stdL_mem_Vset (E := E) n 1).2.1]
  intro y hy
  have := (hΛ.2.1 v).1 hv _ (h (mem_span_smul.2 ⟨y, hy, rfl⟩))
  convert this using 1
  simp only [Base.herm_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [cc]
  ring

variable {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E}
  {A B C : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem sum_reps (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : Good X w A) (hCA : C ≤ A) (hCB : C ≤ B) {c : ℕ} (u : Fin c → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, u i ∈ A) (h2 : ∀ i i', u i - u i' ∈ C → i = i') (h3 : ∀ y ∈ A, ∃ i, y - u i ∈ C)
    {v : TF n g} (hv : IsVac X bas w B v) :
    ∑ i, epsW X w (u i) • heisG X bas (u i) v = (c : ℂ) • projA X bas w A v := by
  obtain ⟨v', hv', -⟩ := hA.vac (bas := bas) hs
  have hsb (i) := rho_sb (w := w) idx hs hn (u i) hv.1
  have hsum (s : Finset (Fin c)) : IsSB (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) ∧
      SW.ip (∑ i ∈ s, epsW X w (u i) • heisG X bas (u i) v) v' = s.card * SW.ip v v' := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨isSB_zero, ?_⟩
      have := ip_smul_left 0 hv'.1 hv'.1
      simpa using this
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ip_add_left (hsb a) ih.1 hv'.1, ih.2, Finset.card_insert_of_notMem ha]
      refine ⟨(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ (hsb a) ih.1).1, ?_⟩
      have := rho_ip (w := w) idx hs hn (u a) hv.1 hv'.1
      rw [hv'.2.2 _ (h1 a)] at this
      rw [this]
      push_cast
      ring
  obtain ⟨k1, k2⟩ := hsum Finset.univ
  rw [hA.uniq hs hv' k1, k2, (hA.proj idx hs hn hv.1 hv').2, smul_smul, Finset.card_univ,
    Fintype.card_fin]
  intro y hy
  choose σ hσ using fun i => h3 (y + u i) (A.add_mem hy (h1 i))
  have hinj : Function.Injective σ := by
    intro i i' h
    apply h2
    have := C.sub_mem (hσ i) (hσ i')
    rw [h] at this
    convert this using 1
    abel
  have hlin (f : Fin c → SW.TF n g) : heisG X bas y (∑ i, f i) = ∑ i, heisG X bas y (f i) := by
    funext x; simp [heisG, heisS, Finset.sum_mul]
  rw [hlin, Finset.smul_sum]
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hA.rho_rho idx hs hn hy (h1 i) hv.1]
  conv_rhs => rw [← hv.2.2 _ (hCB (hσ i))]
  rw [hA.rho_rho idx hs hn (h1 _) (hCA (hσ i)) hv.1, add_sub_cancel]

end

theorem exists_reps_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ N hN hle
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hstd := Base.stdL_mem_Vset (E := E) n 1
  have hA : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hle' := hle
  rw [stdLat_eq] at hle'
  have hsp : Submodule.span E ((Ideal.span {(N : 𝓞 E)} • stdL E n : Lt E n) : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← DualFamily.span_eq_top _ hstd.1 fun x => (hstd.2.1 x).2, Submodule.span_le]
    intro x hx
    have : x = (N : E)⁻¹ • (N • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_span_smul.2 ⟨x, hx, rfl⟩))
  have hidx : (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L).relIndex (tens Λ L) =
      (⟨Λ⟩ : GenLat E n).zCard N r := by
    rw [relIndex_tens_left hL.1 (span_of_selfD X hL) hΛ.1 hsp, GenLat.zCard, stdLat_eq]
    rfl
  have hfin : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 := by
    have hfg : Λ.toAddSubgroup.FG := by
      haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
    haveI : AddGroup.FG Λ.toAddSubgroup := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
    haveI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ.toAddSubgroup
      (mul_ne_zero hN0 hN0)
    have : (nsmulAddMonoidHom (α := Λ.toAddSubgroup) (N * N)).range ≤
        (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup := by
      rintro _ ⟨x, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, stdLat_eq, mem_span_smul]
      exact ⟨N • (x : Fin n → E), nsmul_mem_std hΛ hle' x.2, by simp [mul_smul]⟩
    exact (AddSubgroup.finiteIndex_of_le this).index_ne_zero
  have hz : 0 < (⟨Λ⟩ : GenLat E n).zCard N r := pow_pos (Nat.pos_of_ne_zero hfin) r
  have hm : 0 < (⟨Λ⟩ : GenLat E n).mIdx N r := by
    refine pow_pos (Nat.pos_of_ne_zero fun h => hfin ?_) r
    exact AddSubgroup.relIndex_eq_zero_of_le_right (K := (⟨Λ⟩ : GenLat E n).Ln.toAddSubgroup)
      (fun x hx => hx.1) h
  have hNA : ∀ y ∈ tens Λ L, N • y ∈ tens (stdL E n) L := by
    have : tens Λ L ≤ (tens (stdL E n) L).comap (nsmulAddMonoidHom N) :=
      tens_le fun v hv u hu => by
        rw [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, ← vecMulVec_nsmul]
        exact pure_mem (nsmul_mem_std hΛ hle' hv) hu
    exact fun y hy => this hy
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_even_reps (tens Λ L)
    (tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L) (hN.mul hN)
    (fun y hy => mem_tens_span_smul.2 ⟨_, hNA y hy, by rw [mul_smul]⟩) hidx hz.ne'
  refine ⟨fun i => 2 • a i, fun i => ⟨AddSubgroup.nsmul_mem _ (ha1 i) 2, fun b =>
    ⟨_, (mem_tens_stdL L _).1 (hNA _ (ha1 i)) b, ?_⟩⟩, fun i i' h => ha2 i i' ?_, hz, hm,
    fun v hv => ?_⟩
  · exact smul_comm N 2 (a i b)
  · choose z hz hz' using h
    refine mem_tens_span_smul.2 ⟨z, (mem_tens_stdL L _).2 hz, ?_⟩
    funext b
    exact (hz' b).symm
  · rw [← sum_reps idx hs hn hA (C := tens (Ideal.span {(N : 𝓞 E)} • stdL E n) L)
      (tens_le fun v hv u hu => pure_mem (hle' hv) hu)
      (tens_le fun v hv u hu => pure_mem (Submodule.smul_le_right hv) hu)
      (fun i => 2 • a i) (fun i => AddSubgroup.nsmul_mem _ (ha1 i) 2) ha2 ha3 hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eps_two hs (ha1 i), one_smul]

end GlobalTheory.Dict.ZLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsMoveMarked
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Move

theorem exists_pow_le {E : Type} [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) {d : 𝓞 E} (hd : d ≠ 0) :
    ∃ N : ℕ, ∃ t, IsCoprime (Ideal.span {t}) 𝔪 ∧ ∀ b ∈ 𝔪 ^ N, t * b ∈ Ideal.span {d} := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hd)
  haveI : IsArtinianRing (𝓞 E ⧸ Ideal.span {d}) := isArtinian_of_finite
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := 𝓞 E ⧸ Ideal.span {d}) (M := 𝓞 E ⧸ Ideal.span {d})
    ⟨fun n => OrderDual.toDual ((𝔪 ^ n).map (Ideal.Quotient.mk (Ideal.span {d}))),
      fun a b h => Ideal.map_mono (Ideal.pow_le_pow_right h)⟩
  have h1 : (𝔪 ^ N).map (Ideal.Quotient.mk (Ideal.span {d})) =
      (𝔪 ^ (N + 1)).map (Ideal.Quotient.mk (Ideal.span {d})) := hN (N + 1) (Nat.le_succ N)
  have h2 : 𝔪 ^ N ≤ Ideal.span {d} ⊔ 𝔪 • 𝔪 ^ N := by
    have := (Ideal.le_comap_map (f := Ideal.Quotient.mk (Ideal.span {d})) (I := 𝔪 ^ N))
    rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm, pow_succ'] at this
    exact this
  exact ⟨N, Lev.nakayama (IsNoetherian.noetherian _) h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem exists_pow_smul {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (v : Fin r → E) :
    ∃ N : ℕ, ∀ b ∈ 𝔪 ^ N, b • v ∈ Lev.loc 𝔪 (𝔪 • X.Λ) := by
  obtain ⟨k, hk, hx⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨N, t, ht, h⟩ := exists_pow_le 𝔪 (d := m * (k : 𝓞 E)) (mul_ne_zero hm0 (by exact_mod_cast hk))
  refine ⟨N, fun b hb => ⟨t, ht, ?_⟩⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h b hb)
  rw [← mul_smul, ← hc, mul_smul, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm hx)

omit [IsCMField E] in

theorem isUnit_cols {𝔪 : Ideal (𝓞 E)} (h1 : 𝔪 ≠ ⊤) {L : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {u : Fin r → Fin r → E}
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ 𝔪 • L) : IsUnit (Matrix.of u)ᵀ := by
  obtain ⟨s, hs, hN⟩ := Lev.nakayama hfg h
  have hs0 : (s : E) ≠ 0 := by simpa using Lev.cop_ne_zero h1 hs
  have hli : LinearIndependent E u := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← hsp, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  exact Matrix.linearIndependent_cols_iff_isUnit.1 hli

theorem exists_cong (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hL : SelfD X L)
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧
      ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  obtain ⟨U, hU⟩ := isUnit_cols D.proper hL.1 (TensLat.span_of_selfD X hL) h
  obtain ⟨B, hB⟩ := isUnit_cols D.proper X.Λ_fg X.Λ_span D.β_span
  have hA (i) : ((B * U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u i = D.β i := by
    have e1 : u i = (U : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1 := by
      rw [hU]; funext k; simp
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, hB]
    funext k; simp
  choose N hN using fun p : Fin r × Fin r × Fin r =>
    exists_pow_smul (X := X) D.ne_bot (Pi.single p.2.1 (u p.1 p.2.2))
  obtain ⟨ga, hu, s, hs, hb⟩ := GlobalTheory.T.strong_approximation_unitary_congruence E r X D.𝔪 D.ne_bot D.cop (B * U⁻¹) (Finset.univ.sup N)
  choose b hb e using hb
  refine ⟨ga, hu, fun i => Lev.cong_iff.2 (Lev.loc_loc hs ?_)⟩
  have e2 : s • ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i - D.β i) =
      ∑ k, ∑ j, b k j • (Pi.single k (u i j) : Fin r → E) := by
    rw [← hA]
    funext k
    simp only [Lev.O_smul, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply,
      Matrix.mulVec, dotProduct, ← e]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk => by rw [if_neg (Ne.symm hk), mul_zero]) (by simp), if_pos rfl]
    change (s : E) * _ = _
    ring
  rw [e2]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    hN (i, k, j) _ (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) (hb k j))

theorem mem_lats (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hΛ : SelfD X X.Λ) (hL : SelfD X L)
    (hu : ∀ i, u i ∈ L) (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L)
    (hc : ∀ i, Cong X D.𝔪 (u i) (D.β i)) : L ∈ D.lats := by
  have h1 : L ≤ Lev.loc D.𝔪 X.Λ := by
    obtain ⟨s, hs, hN⟩ := Lev.nakayama hL.1 h
    intro v hv
    refine Lev.loc_loc hs (Submodule.span_le.2 ?_ (hN v hv))
    rintro _ ⟨i, rfl⟩
    have := add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 (hc i)))
      (Lev.le_loc _ (D.β_mem i))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ L ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine Lev.mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (Lev.loc_mono (le_sup_right (a := L)) (Lev.cong_iff.1 (Lev.cong_symm (hc i))))
      (Lev.le_loc _ (Submodule.mem_sup_left (hu i)))
    rwa [sub_add_cancel] at this
  obtain ⟨s, hs, h1⟩ := Lev.exists_mul_of_fg hL.1 h1
  obtain ⟨t, ht, h2⟩ := Lev.nakayama X.Λ_fg h2
  have h1' (v) (hv : v ∈ L) : Lev.bar t • v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hL.2 _).1 hv _ (h2 y hy)
  have h2' (v) (hv : v ∈ X.Λ) : Lev.bar s • v ∈ L := (hL.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hΛ.2 _).1 hv _ (h1 y hy)
  obtain ⟨a, b, hab⟩ := Lev.cop_glue D.cop hs (Lev.cop_bar ht)
  obtain ⟨a', b', hab'⟩ := Lev.cop_glue D.cop ht (Lev.cop_bar hs)
  refine ⟨hL, _, Lev.cop_mul hab hab', fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_comm, mul_smul]
    refine X.Λ.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (X.Λ.smul_mem _ (h1 v hv)) (X.Λ.smul_mem _ (h1' v hv))
  · rw [mul_smul]
    refine L.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (L.smul_mem _ (h2 v hv)) (L.smul_mem _ (h2' v hv))

end GlobalTheory.Dict.Move

theorem GlobalTheory.Dict.exists_move_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (D : SW.Level X) (L : Lt E r) (u : Fin r → Fin r → E), SelfD X X.Λ → SelfD X L → (∀ i, u i ∈ L) → L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L → ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  intro E _ _ _ r X D L u hΛ hL hu h
  obtain ⟨ga, hun, hc⟩ := Move.exists_cong D hL h
  refine ⟨ga, hun, Move.mem_lats D (u := fun i => Lev.lin ga (u i)) hΛ (Lev.selfD_mapL hun hL)
    (fun i => ⟨_, hu i, rfl⟩) ?_ hc, hc⟩
  refine (Submodule.map_mono (f := Lev.lin ga) h).trans ?_
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'']
  exact le_rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticDoubledHermitianCoordinates
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem cc_cc (a : E) : cc (cc a) = a := by
  unfold cc
  exact IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a := by
  unfold cc
  exact Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem sum_trace {ι : Type} [Fintype ι] (B : Module.Basis ι ℚ E) (b d : E) :
    ∑ j, Algebra.trace ℚ E (b * cc (B j)) * B.repr d j = Algebra.trace ℚ E (b * cc d) := by

  have hd : cc d = ∑ j, B.repr d j • cc (B j) := by
    conv_lhs => rw [← B.sum_repr d]
    unfold cc
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_rat_smul _ _ _
  rw [hd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

theorem vec_inl (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = y₁ a - y₂ a := by
  simp [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

theorem vec_inr (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) = X.κ0 / 4 * ∑ c, (y₁ c + y₂ c) * X.Gm c a := by
  simp only [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem split_form (y₁ y₂ z₁ z₂ : Fin r → E) :
    ∑ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inl a)) -
      ∑ a, cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inr a)) * (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) =
      -(X.κ0 / 2) * herm X.Gm y₂ z₂ - -(X.κ0 / 2) * herm X.Gm y₁ z₁ := by

  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by unfold cc; exact map_add _ a b
  have hsub : ∀ a b : E, cc (a - b) = cc a - cc b := fun a b => by unfold cc; exact map_sub _ a b
  have hsum : ∀ f : Fin r → E, cc (∑ c, f c) = ∑ c, cc (f c) := fun f => by
    unfold cc; exact map_sum _ _ _
  have hk : cc (X.κ0 / 4) = -(X.κ0 / 4) := by
    have h4 : cc (4 : E) = 4 := by unfold cc; exact map_ofNat _ 4
    have hd : cc (X.κ0 / 4) = cc X.κ0 / cc 4 := by unfold cc; exact map_div₀ _ _ _
    rw [hd, h4, DblPer.cc_kappa X, neg_div]
  simp only [vec_inl, vec_inr, cc_mul, hadd, hsub, hsum, hk, X.Gm_herm, herm]
  simp only [Finset.mul_sum, Finset.sum_mul]

  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

noncomputable def dv (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) : Fin r ⊕ Fin r → E :=
  Sum.elim (vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)))
    (vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)))) ᵥ* dblT X

theorem dv_add (u v) : dv X bas (u + v) = dv X bas u + dv X bas v := by
  have h₁ : Sum.elim ((u + v).1 ∘ Sum.inl) ((u + v).2 ∘ Sum.inl) =
      Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) + Sum.elim (v.1 ∘ Sum.inl) (v.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((u + v).1 ∘ Sum.inr) (-((u + v).2 ∘ Sum.inr)) =
      Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) + Sum.elim (v.1 ∘ Sum.inr) (-(v.2 ∘ Sum.inr)) := by
    ext (i | i)
    · rfl
    · simp only [Sum.elim_inr, Pi.neg_apply, Function.comp_apply, Prod.snd_add, Pi.add_apply]
      ring
  unfold dv
  rw [h₁, h₂, vecQ_add, vecQ_add, ← Matrix.add_vecMul, Sum.elim_add_add]

theorem dv_smul (q : ℚ) (u) : dv X bas (q • u) = q • dv X bas u := by
  have h₁ : Sum.elim ((q • u).1 ∘ Sum.inl) ((q • u).2 ∘ Sum.inl) =
      q • Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((q • u).1 ∘ Sum.inr) (-((q • u).2 ∘ Sum.inr)) =
      q • Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) := by
    ext (i | i) <;> simp
  have h₃ : ∀ f g' : Fin r → E, Sum.elim (q • f) (q • g') = q • Sum.elim f g' := fun f g' => by
    ext (i | i) <;> rfl
  unfold dv
  rw [h₁, h₂, vecQ_smul, vecQ_smul, h₃, Matrix.smul_vecMul]

noncomputable def crdMap : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ]
    ((QI E r → ℚ) × (QI E r → ℚ)) where
  toFun u := (fun p => Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)),
    fun p => (Module.finBasis ℚ E).repr (dv X bas u (Sum.inl p.1)) p.2)
  map_add' u v := by
    ext p <;> simp [dv_add, add_mul]
  map_smul' q u := by
    ext p <;> simp [dv_smul]

theorem crdMap_pair (u v) : (crdMap X bas u).1 ⬝ᵥ (crdMap X bas v).2 =
    Algebra.trace ℚ E (∑ a, dv X bas u (Sum.inr a) * cc (dv X bas v (Sum.inl a))) := by
  have e₁ : ∀ p : QI E r, (crdMap X bas u).1 p =
      Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)) := fun p => rfl
  have e₂ : ∀ p : QI E r, (crdMap X bas v).2 p =
      (Module.finBasis ℚ E).repr (dv X bas v (Sum.inl p.1)) p.2 := fun p => rfl
  simp only [dotProduct, e₁, e₂]
  rw [Fintype.sum_prod_type, map_sum (Algebra.trace ℚ E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [sum_trace (Module.finBasis ℚ E) (dv X bas u (Sum.inr a)) (dv X bas v (Sum.inl a))]

theorem dbl_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  intro E _ _ _ r X g bas hs
  refine ⟨crdMap X bas, fun u v => ?_, fun u y₁ y₂ h₁ h₂ => ?_⟩
  ·
    have hsum : ∀ f : Fin r → E, cc (∑ a, f a) = ∑ a, cc (f a) := fun f => by
      unfold cc; exact map_sum _ _ _
    have hsw : (crdMap X bas u).2 ⬝ᵥ (crdMap X bas v).1 =
        Algebra.trace ℚ E (∑ a, cc (dv X bas v (Sum.inr a)) * dv X bas u (Sum.inl a)) := by
      rw [dotProduct_comm, crdMap_pair, ← trace_cc, hsum]
      simp only [cc_mul, cc_cc]
    rw [crdMap_pair, hsw, ← map_sub]
    unfold dv
    rw [split_form, map_sub, ← EF_def, ← EF_def, EF_vecQ hs, EF_vecQ hs]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.neg_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_neg, neg_mul]
    ring
  · subst h₁ h₂
    exact ⟨fun a => ((Module.finBasis ℚ E).sum_repr _).symm, fun a j => rfl⟩

end GlobalTheory.SW.DblLat
end

