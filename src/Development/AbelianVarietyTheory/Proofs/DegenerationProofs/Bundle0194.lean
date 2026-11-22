import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfMemKL
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CyclicDescent

open ThetaSplit

section Bundles

variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_gen_scale {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (b : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J * gm r z ⊤ b := by
  refine ⟨⟨fun i => t.s i * res le_top b⟩, ?_, ?_⟩
  · unfold LB.Gen.IsGen at ht ⊢
    intro i j
    simp only [map_mul, LB.res_res]
    rw [ht i j]
    exact mul_assoc _ _ _
  · intro Z r z J hJ
    refine (map_mul (gm r z _) _ _).trans ?_
    congr 1
    exact gm_res r z _ (hJ.mem φ r) b

theorem exists_gen_iterate (hL : L.IsLB) (τ : ℕ → (X ⟶ X)) (h0 : τ 0 = 𝟙 X) (hτ : ∀ i, τ (i + 1) = τ i ≫ τ 1)
    (v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ 1] ![1, -1])) (hv : v.IsGen) (j : ℕ) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ j] ![1, -1]), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val w r z J = ∏ i ∈ Finset.range j, val v (r ≫ τ i) z J := by
  induction j with
  | zero =>
    have hF : FormEq (PEmpty.elim : PEmpty → (X ⟶ X)) PEmpty.elim ![𝟙 X, τ 0] ![(1 : ℤ), -1] := by
      intro U _ h
      simp [Fin.prod_univ_two, h0]
    obtain ⟨w, hw, hw'⟩ := exists_gen hL hF (LB.oneGen L (Y := X)) (LB.isGen_oneGen L)
    refine ⟨w, hw, fun Z r z J hJ => ?_⟩
    rw [hw' Z r z J hJ, val_one]
    simp
  | succ j ih =>
    obtain ⟨w, hw, hw'⟩ := ih
    have hp := LB.isGen_pullGen L _ _ v hv (τ j)
    have hm := LB.isGen_mulGen L ![𝟙 X, τ j] ![1, -1] (fun k => τ j ≫ ![𝟙 X, τ 1] k) ![1, -1] w
      (L.pullGen ![𝟙 X, τ 1] ![1, -1] v (τ j)) hw hp
    have hF : FormEq (Sum.elim ![𝟙 X, τ j] (fun k => τ j ≫ ![𝟙 X, τ 1] k)) (Sum.elim ![(1 : ℤ), -1] ![1, -1])
        ![𝟙 X, τ (j + 1)] ![(1 : ℤ), -1] := by
      intro U _ h
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, Category.comp_id, ← hτ]
      group
    obtain ⟨w', hw'', hv'⟩ := exists_gen hL hF _ hm
    refine ⟨w', hw'', fun Z r z J hJ => ?_⟩
    rw [hv' Z r z J hJ, val_mul hJ, val_pull hJ, hw' Z r z J hJ, Finset.prod_range_succ]

end Bundles

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem exists_gen_of_memKL {L : LB A.left} (hL : L.IsLB) [Subsingleton S] [Nonempty S]
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x) :
    ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl x] ![1, -1]), v.IsGen := by
  obtain ⟨p⟩ := ‹Nonempty S›
  obtain ⟨V, hpV, c, hc⟩ := hx p
  have : Subsingleton ↥(𝟙_ (Over S)).left := ‹Subsingleton ↥S›
  have hW : ∀ y, y ∈ (fst (𝟙_ (Over S)) A).left ⁻¹ᵁ V := fun y => by
    show (fst (𝟙_ (Over S)) A).left y ∈ V
    rwa [Subsingleton.elim ((fst (𝟙_ (Over S)) A).left y) p]
  obtain ⟨t, ht⟩ := GlobalTheory.TwistTranslate.gen_of_pull_top hL _ hW c hc
  have h1 := LB.isGen_invGen L _ _ (LB.pullGen L _ _ t (lift (toUnit A) (𝟙 A)).left)
    (LB.isGen_pullGen L _ _ t ht (lift (toUnit A) (𝟙 A)).left)
  have ea : (lift (toUnit A) (𝟙 A)).left ≫ (lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left =
      ThetaSplit.transl x := by
    rw [← Over.comp_left]
    congr 1
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
    rfl
  have eb : (lift (toUnit A) (𝟙 A)).left ≫ (snd (𝟙_ (Over S)) A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have hF : FormEq (fun k => (lift (toUnit A) (𝟙 A)).left ≫
      ![(lift (fst (𝟙_ (Over S)) A ≫ x) (snd _ A) ≫ μ).left, (snd (𝟙_ (Over S)) A).left] k)
      (fun k => -![(1 : ℤ), -1] k) ![𝟙 A.left, ThetaSplit.transl x] ![(1 : ℤ), -1] := by
    intro U _ h
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ea, eb]
    simp [mul_comm]
  obtain ⟨v, hv, -⟩ := exists_gen hL hF _ h1
  exact ⟨v, hv⟩

theorem exists_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    [Subsingleton S] [Nonempty S] (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S, ⊤)ˣ, ∃ x : Γ(S, ⊤)ˣ, x ^ n = y)
    {x : 𝟙_ (Over S) ⟶ A} (hx : MemKL A L x)
    {C : Type} [CommGroup C] (i : C →* (𝟙_ (Over S) ⟶ A)) (hi : ∀ c, ∃ j : ℕ, x ^ j = i c) :
    ∃ u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
        (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (ThetaSplit.transl (i c)))) := by
  have : IsCommMonObj A := hA.comm
  have e1 : toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A) = 1 := comp_one (toUnit A)
  have h0 : ThetaSplit.transl (x ^ 0) = 𝟙 A.left := by
    rw [pow_zero]
    show ((toUnit A ≫ (1 : 𝟙_ (Over S) ⟶ A)) * 𝟙 A).left = 𝟙 A.left
    rw [e1, _root_.one_mul (𝟙 A : A ⟶ A)]
    rfl
  have hτ : ∀ m : ℕ, ThetaSplit.transl (x ^ (m + 1)) = ThetaSplit.transl (x ^ m) ≫ ThetaSplit.transl (x ^ 1) := by
    intro m
    rw [pow_succ, pow_one, ThetaSplit.transl_mul]
  obtain ⟨v, hv⟩ : ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (x ^ 1)] ![1, -1]),
      v.IsGen := by
    rw [pow_one]
    exact exists_gen_of_memKL hL hx
  choose j hj using hi
  have hw : ∀ c, ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val w r z J = ∏ m ∈ Finset.range (j c), val v (r ≫ ThetaSplit.transl (x ^ m)) z J := by
    intro c
    rw [← hj c]
    exact exists_gen_iterate hL (fun m => ThetaSplit.transl (x ^ m)) h0 hτ v hv (j c)
  choose w hwg hwv using hw
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (a m : ℕ),
      (r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m) = r ≫ ThetaSplit.transl (x ^ (a + m)) := by
    intro Z r a m
    rw [pow_add, ThetaSplit.transl_mul, Category.assoc]
  have hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
      val (w c) r z J * val (w c') (r ≫ ThetaSplit.transl (i c)) z J =
        val (w c') r z J * val (w c) (r ≫ ThetaSplit.transl (i c')) z J := by
    intro c c' Z r z J hJ
    have hs : ∀ a b, ∏ m ∈ Finset.range (a + b), val v (r ≫ ThetaSplit.transl (x ^ m)) z J =
        (∏ m ∈ Finset.range a, val v (r ≫ ThetaSplit.transl (x ^ m)) z J) *
          ∏ m ∈ Finset.range b, val v ((r ≫ ThetaSplit.transl (x ^ a)) ≫ ThetaSplit.transl (x ^ m)) z J := by
      intro a b
      rw [Finset.prod_range_add]
      simp only [key]
    rw [hwv c Z r z J hJ, hwv c' Z r z J hJ, hwv c' Z _ z J hJ, hwv c Z _ z J hJ, ← hj c, ← hj c', ← hs, ← hs,
      add_comm]
  obtain ⟨b, hb⟩ := ThetaSplit.exists_rescale hL A.hom η[A].left (Over.w η[A]) (hG S A hA).2 hU
    (fun c => ThetaSplit.transl (i c)) (fun c c' => by simp only [map_mul, ThetaSplit.transl_mul])
    (fun c => ThetaSplit.transl_hom (i c)) 1 w hwg hc
  have gmtop_lemma : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) (z : Z) (c : Γ(S, ⊤)ˣ),
      gm r z ⊤ (Units.map A.hom.appTop.hom c) = gm (r ≫ A.hom) z ⊤ c := by
    intro Z r z c
    unfold gm
    rw [dif_pos (show r z ∈ (⊤ : A.left.Opens) from trivial),
      dif_pos (show (r ≫ A.hom) z ∈ (⊤ : S.Opens) from trivial)]
    ext
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, pullU]
    rfl
  have hu : ∀ c, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ThetaSplit.transl (i c)] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val u r z J = val (w c) r z J * gm (r ≫ A.hom) z ⊤ (b c) := by
    intro c
    obtain ⟨u, hu, hsc⟩ := exists_gen_scale (w c) (hwg c) (Units.map A.hom.appTop.hom (b c))
    refine ⟨u, hu, fun Z r z J hJ => ?_⟩
    rw [hsc Z r z J hJ, gmtop_lemma]
  choose u hug huv using hu
  refine ⟨u, hug, fun c c' => corr_of_val hL (fun y J hJ => ?_)⟩
  rw [val_mul hJ, val_pull hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, huv _ _ _ _ _ hJ, Category.assoc,
    ThetaSplit.transl_hom]
  exact hb c c' _ (𝟙 _) y J hJ

end Group

theorem exists_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (x : (𝟙_ (Over (Sp k)) ⟶ A)) (n : ℕ), 1 ≤ n → orderOf x = n → GlobalTheory.MemKL A L x → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (y : Over.mk t ⟶ A), y ≫ ψ = 1 ↔ ∃ c ∈ Subgroup.zpowers x, y = toUnit _ ≫ c) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) := by
  intro k _ _ A B _ _ hA L hL x n hn hord hx ψ hψ _ _ _ hker
  have : IsCommMonObj A := hA.comm
  have hfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hord]
    omega
  have : Finite (Subgroup.zpowers x) := by
    exact (finite_zpowers.mpr hfin).to_subtype
  have hi : ∀ c : Subgroup.zpowers x, ∃ j : ℕ, x ^ j = (Subgroup.zpowers x).subtype c := fun c =>
    (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr c.2)
  obtain ⟨u, hu, hcoc⟩ := exists_cocycle globalFns_holds hA hL (ThetaSplit.units_divisible k) hx
    (Subgroup.zpowers x).subtype hi
  refine GlobalTheory.LinDescent.exists_descent_of_isReduced (Sp k) A B ψ (Subgroup.zpowers x) (Subgroup.zpowers x).subtype
    L hL hψ ‹_› ‹_› ‹_› ?_ u hu hcoc
  intro k' _ _ t
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · rw [hker k' t y]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.2, rfl⟩
  · have e : (toUnit (Over.mk t)).left = t := by simp
    have : Epi (toUnit (Over.mk t)).left := e ▸ ThetaSplit.epi_of_fields t
    have : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
    have hc' : toUnit (Over.mk t) ≫ (c : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := hc
    apply Subtype.ext
    apply (cancel_epi (toUnit (Over.mk t))).mp
    rw [hc', Subgroup.coe_one, comp_one]

end GlobalTheory.CyclicDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.EighthPowerFactor

open CechPic

theorem relAmple_diag_lam {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hN : ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hι : (M.pull ((𝟙 B)⁻¹ : B ⟶ B).left).IsLB := pull_isLB hM _
  have hD1 : (LB.div ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) M).IsLB := LB.isLB_div hN hM
  have hD := LB.isLB_div hD1 hι
  haveI : IsProper B.hom := IsAbelianScheme.proper
  have hI : ((𝟙 B)⁻¹ : B ⟶ B) ≫ (𝟙 B)⁻¹ = 𝟙 B := by
    first
    | rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    | rw [GrpObj.inv_def, Category.id_comp, GrpObj.inv_inv]
    | simp [GrpObj.comp_inv]
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := ⟨⟨_, hI, hI⟩⟩
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left :=
    ⟨⟨((𝟙 B)⁻¹ : B ⟶ B).left, by rw [← Over.comp_left, hI, Over.id_left],
      by rw [← Over.comp_left, hI, Over.id_left]⟩⟩
  have h0 : ∀ (L : LB (Sp k)), L.IsLB → ∃ t : LB.Gen L, t.IsGen := by
    intro L hL
    have hcov : ∀ y : Sp k, ∃ i, y ∈ L.U i := fun y => by
      have hy : y ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hy
    have hs : ∀ y y' : Sp k, y = y' := fun y y' => Subsingleton.elim (α := PrimeSpectrum k) y y'
    obtain ⟨y₀⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    obtain ⟨i₀, hi₀⟩ := hcov y₀
    exact GlobalTheory.DescendedPrincipal.exists_gen_of_chart hL i₀ fun y => by rw [← hs y₀ y]; exact hi₀
  set c := GlobalTheory.CechPic.cls M hM
  have e1 : (1 : B ⟶ B).left = (toUnit B).left ≫ η[B].left := rfl
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left c = 0 := by
    rw [e1, GlobalTheory.CechPic.pull_comp]
    obtain ⟨L, hL, hLc⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull η[B].left c)
    rw [← hLc, (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (h0 L hL), map_zero]
  have e5 : GlobalTheory.CechPic.lam c (𝟙 B)⁻¹ (𝟙 B) = -GlobalTheory.CechPic.pull ((𝟙 B)⁻¹ : B ⟶ B).left c - c := by
    unfold GlobalTheory.CechPic.lam
    rw [inv_mul_cancel, Over.id_left, GlobalTheory.CechPic.pull_id, h1]
    abel
  have e3 := GlobalTheory.CechPic.lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, GlobalTheory.CechPic.lam_one_left, e5] at e3
  have e2 : GlobalTheory.CechPic.cls (abelian₂ B M) (LB.isLB_linComb hM _ _) = GlobalTheory.CechPic.lam c (fst B B) (snd B B) :=
    GlobalTheory.CechPic.cls_cube_two hM _ _ _
  have hc : GlobalTheory.CechPic.cls _ hD = 0 := by
    rw [GlobalTheory.CechPic.cls_div hD1 hι hD, GlobalTheory.CechPic.cls_div hN hM hD1,
      GlobalTheory.CechPic.cls_pull (L := abelian₂ B M) (LB.isLB_linComb hM _ _) _ hN, GlobalTheory.CechPic.cls_pull hM _ hι, e2,
      GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
    rw [eq_comm, ← sub_eq_zero] at e3
    rw [← e3]
    abel
  have H := (GlobalTheory.CechPic.cls_eq_zero_iff hD).1 hc
  have hMa := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hM).1 ha
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 (hMa.tensor (hMa.pull_of_isFinite _) hN H)

theorem weilIs_one_one (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} (hM : M.IsLB) (T : Over S) : Out.WeilIs A M 1 (1 : T ⟶ A) 1 1 := by
  refine GlobalTheory.DescendedPrincipal.weilIs_one_right hG hA hM fun _ => ⟨⊤, trivial, ?_⟩
  exact match GlobalTheory.DescendedPrincipal.exists_theta_one (A := A) hM _ with
  | ⟨θ, hθ, _⟩ => ⟨θ, hθ.trans (MonObj.comp_one _).symm⟩

open SiegelOfPolarised PrimNorm in

def siegOne (hG : Out.GlobalFnsSt) {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : kˣ) : k) (𝟙 (Sp k)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : (W + W.transpose).det = 1) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  have hu : IsUnit (W + W.transpose).det := by rw [hW]; exact isUnit_one
  refine ⟨fun j => Sum.elim (fun p => Matrix.single p.1 p.2 1)
      (fun b => if b then (W + W.transpose)⁻¹ * W else (W + W.transpose)⁻¹ * W.transpose) j,
    Sum.inr true, Sum.inr false, ?_, ?_, fun u v => ⟨Sum.inl (u, v), rfl⟩⟩
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]

theorem isMonHom_of_coord {S : Scheme.{0}} {A G X : Over S} [GrpObj A] [GrpObj G] [GrpObj X] {n : ℕ}
    {pr : Fin n → (G ⟶ A)} (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) {f : X ⟶ G}
    (hf : ∀ u, IsMonHom (f ≫ pr u)) : IsMonHom f := by
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun x x' h =>
    (hu _ (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  constructor
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

theorem exists_polAV_hypS_retract : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Out.KTriv B M → ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  intro k _ _ B _ g hB hd M hM ha hK
  obtain ⟨hL1, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG : Out.GlobalFnsSt := hL1.globalFns
  letI : IsCommMonObj B := hB.comm
  have hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen := GlobalTheory.exists_gen_theta_of_isAbelianScheme k B hB M hM
  let b : GlobalTheory.ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp [IsPrimitiveRoot.one]⟩
  let c := siegOne hG hB hM g
  have hc : c.Principal :=
    ⟨relAmple_diag_lam hB hM hΘ ha, fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  obtain ⟨t, hsh, hp⟩ := GlobalTheory.exists_isSharp_and_prim hL1 hL2 GlobalTheory.Moduli.cube_of_isLB g (8 * g) W _ a w w' bas
    hW hb hw hw' hs 1 k b (Sp k) (𝟙 _) c (show (1 : kˣ) ^ 1 = 1 from one_pow 1) odd_one hc hd
  obtain ⟨pr, hpr, hu, -, -, -⟩ := hsh
  obtain ⟨i, hi, -⟩ := hu B (fun _ => 𝟙 B)
  letI := t.ab.comm
  refine ⟨t.pol, i, pr 0, ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩, ?_, hpr 0, hi 0⟩
  exact isMonHom_of_coord hpr hu (fun u => by rw [hi u]; exact (inferInstance : IsMonHom (𝟙 B)))

end GlobalTheory.EighthPowerFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteMulKTriv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.KTrivPoints

theorem finite_mul_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x} ∧ (∀ x y : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → GlobalTheory.MemKL B M y → GlobalTheory.MemKL B M (x * y)) ∧ ((∀ x : (𝟙_ (Over (Sp k)) ⟶ B), GlobalTheory.MemKL B M x → x = 1) → Out.KTriv B M) := by
  intro k _ _ _ B _ hB M hM hA
  obtain ⟨H, j, hj, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have := hB.comm
  refine ⟨?_, fun x y hx hy => GlobalTheory.UU.InK.mul hM hx hy, fun hx => ?_⟩
  · have : IsFinite (toUnit H).left := hfin
    have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
    refine Finite.of_surjective
      (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} =>
        (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : (𝟙_ (Over (Sp k)) ⟶ B) // GlobalTheory.MemKL B M x})) fun x => ?_
    obtain ⟨z, hz⟩ := (hH _ _).1 x.2
    exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩
  · have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
    have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hH _ _).1 (GlobalTheory.memKL_one hM _))
      (fun T x y => (hH _ _).1 (GlobalTheory.UU.InK.mul hM ((hH _ _).2 ⟨x, rfl⟩)
        (GlobalTheory.UU.InK.inv hM ((hH _ _).2 ⟨y, rfl⟩))))
      k (𝟙 _) (fun x => hx _ ((hH _ _).2 ⟨x, rfl⟩))
    refine GlobalTheory.UU.kTriv_iff_forall.2 fun T x hxK => ?_
    obtain ⟨y, rfl⟩ := (hH T x).1 hxK
    exact key T (toUnit T) y

end GlobalTheory.KTrivPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.nonempty_level_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (M : ℕ) (ze : kˣ), (M : k) ≠ 0 → IsPrimitiveRoot ze M → Nonempty (Out.Level P M (unitOn ze)) := by
  intro k _ _ P M ze hM hz
  have hz0 : IsPrimitiveRoot (ze : k) M := IsPrimitiveRoot.coe_units_iff.mpr hz

  have hinj : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Sp k),
      Function.Injective ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    intro K _ s
    exact Function.Injective.of_comp
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
        ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    fun a b h => hinj k (𝟙 _) (by rw [RingHom.comp_apply, RingHom.comp_apply, h])

  have hu : IsPrimitiveRoot (unitOn ze) M := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz0.map_of_injective hinv
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.ConstThetaLevel.exists_symplectic_points hL k P rfl M hM (unitOn ze) hu

  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing GlobalTheory.globalFns_holds hL.weil hL.mulN (Sp k) P M (unitOn ze) hu
    (fun K _ s => by
      refine ⟨fun h0 => hM ?_, ?_⟩
      · have hf := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
          ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
        exact hf (by rw [map_natCast, map_zero]; exact h0)
      · rw [← IsPrimitiveRoot.coe_units_iff]
        exact hz0.map_of_injective (hinj K s))
    x hx1 hx2
  exact ⟨lev⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanishStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OnModel.theta_on_model | exact GlobalTheory.Ex.OnModel.theta_on_model | (intros; apply GlobalTheory.Ex.OnModel.theta_on_model <;> assumption)
end

