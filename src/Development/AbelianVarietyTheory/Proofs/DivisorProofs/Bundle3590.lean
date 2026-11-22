import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3582
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0823
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3583

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffine
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechH1Span

theorem resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

set_option maxHeartbeats 1000000 in

theorem exists_dlog_add_coboundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj c hc
  let ρ : ∀ p : J × J, Γ(X, U.1) →+* Γ(t.G.left, W p.1 ⊓ W p.2) := fun p =>
    (t.G.hom.appLE U.1 (W p.1 ⊓ W p.2) (inf_le_left.trans (hWU p.1))).hom
  letI inst : ∀ p : J × J, Module Γ(X, U.1) Γ(t.G.left, W p.1 ⊓ W p.2) := fun p => Module.compHom _ (ρ p)
  have smul_apply : ∀ (r : Γ(X, U.1)) (x : ∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) (p : J × J),
      (r • x) p = ρ p r * x p := fun _ _ _ => rfl
  let Z : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (x (i, i')) +
          resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
            (x (i', i'')) =
          resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
            (x (i, i''))}
      add_mem' := by
        intro a b ha hb i i' i''
        simp only [Pi.add_apply, map_add]
        rw [← ha i i' i'', ← hb i i' i'']
        abel
      zero_mem' := by
        intro i i' i''
        simp
      smul_mem' := by
        intro r x hx i i' i''
        simp only [smul_apply, map_mul]
        rw [← hx i i' i'']
        simp only [ρ, resG_appLE]
        ring }
  let Bd : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    { carrier := {x | ∃ h : ∀ i : J, Γ(t.G.left, W i), ∀ i i',
          x (i, i') = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i')}
      add_mem' := by
        rintro a b ⟨h1, e1⟩ ⟨h2, e2⟩
        refine ⟨h1 + h2, fun i i' => ?_⟩
        simp only [Pi.add_apply, map_add, e1, e2]
        ring
      zero_mem' := ⟨0, fun i i' => by simp⟩
      smul_mem' := by
        rintro r x ⟨h1, e1⟩
        refine ⟨fun i => (t.G.hom.appLE U.1 (W i) (hWU i)).hom r * h1 i, fun i i' => ?_⟩
        simp only [smul_apply, e1, map_mul, resG_appLE, ρ]
        ring }
  let κ : Fin n → (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) := fun b p =>
    δ b (W p.1 ⊓ W p.2) (resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2)).val) *
      resG t.G.left (inf_le_inf (hj p.1) (hj p.2)) (t.PP.L.g (j p.1) (j p.2))⁻¹.val
  let S : Submodule Γ(X, U.1) (∀ p : J × J, Γ(t.G.left, W p.1 ⊓ W p.2)) :=
    Bd ⊔ Submodule.span Γ(X, U.1) (Set.range κ)
  let S' : Submodule Γ(X, U.1) Z := S.comap Z.subtype
  obtain ⟨N, e, he, hAe⟩ := GlobalTheory.T.cech_h1_finite_generation_affine E H X t hP hA U J W hWa hcov hWU
  let ek : Fin N → Z := fun k => ⟨fun p => e k p.1 p.2, he k⟩
  have hspan : Submodule.span Γ(X, U.1) (Set.range fun k => S'.mkQ (ek k)) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨r, h, hz⟩ := hAe (fun i i' => z.1 (i, i')) (z.2)
    have hmem : z - ∑ k, r k • ek k ∈ S' := by
      refine Submodule.mem_sup_left ⟨h, fun i i' => ?_⟩
      change z.1 (i, i') - (∑ k, r k • ek k).1 (i, i') = _
      rw [Submodule.coe_sum, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ]
      exact add_sub_cancel_right _ _
    have : S'.mkQ z = ∑ k, r k • S'.mkQ (ek k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite Γ(X, U.1) (Z ⧸ S') := ⟨⟨Finset.univ.image fun k => S'.mkQ (ek k), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan⟩⟩
  have hbot := GlobalTheory.submodule_eq_top_of_sup_maximal_smul_eq_top Γ(X, U.1) (Z ⧸ S') ⊥ (fun m hm => by
    rw [bot_sup_eq]
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨z, rfl⟩ := S'.mkQ_surjective q
    obtain ⟨θ, h, N', r, e', hr, he', hz⟩ :=
      GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_mod E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
        (fun i i' => z.1 (i, i')) z.2
    let ek' : Fin N' → Z := fun k => ⟨fun p => e' k p.1 p.2, he' k⟩
    have hmem : z - ∑ k, r k • ek' k ∈ S' := by
      have hw : ∑ b, θ b • κ b ∈ Submodule.span Γ(X, U.1) (Set.range κ) :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
      have hy : (fun p : J × J => resG t.G.left (inf_le_left : W p.1 ⊓ W p.2 ≤ W p.1) (h p.1) -
          resG t.G.left (inf_le_right : W p.1 ⊓ W p.2 ≤ W p.2) (h p.2)) ∈ Bd := ⟨h, fun i i' => rfl⟩
      change (z - ∑ k, r k • ek' k : Z).1 ∈ S
      refine Submodule.mem_sup.2 ⟨_, hy, _, hw, ?_⟩
      funext p
      obtain ⟨i, i'⟩ := p
      change _ = z.1 (i, i') - (∑ k, r k • ek' k).1 (i, i')
      rw [Submodule.coe_sum, Finset.sum_apply, Pi.add_apply, Finset.sum_apply, hz i i']
      simp only [Submodule.coe_smul, smul_apply, ρ, κ]
      exact (add_sub_cancel_right _ _).symm
    have hq : S'.mkQ z = ∑ k, r k • S'.mkQ (ek' k) := by
      have h0 : S'.mkQ (z - ∑ k, r k • ek' k) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hmem
      rw [map_sub, map_sum] at h0
      simp only [map_smul] at h0
      exact sub_eq_zero.1 h0
    rw [hq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hr k) Submodule.mem_top)
  let cz : Z := ⟨fun p => c p.1 p.2, hc⟩
  have hcz : S'.mkQ cz = 0 := by
    have : S'.mkQ cz ∈ (⊥ : Submodule Γ(X, U.1) (Z ⧸ S')) := hbot ▸ Submodule.mem_top
    exact (Submodule.mem_bot _).1 this
  have hcS0 : cz ∈ S' := (Submodule.Quotient.mk_eq_zero S').1 hcz
  have hcS : cz.1 ∈ S := hcS0
  obtain ⟨y, ⟨h, hy⟩, w, hw, hyw⟩ := Submodule.mem_sup.1 hcS
  obtain ⟨θ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw
  refine ⟨θ, h, fun i i' => ?_⟩
  have k := congrFun hyw (i, i')
  change _ = c i i' at k
  rw [← k, Pi.add_apply, hy i i', Finset.sum_apply]
  simp only [smul_apply, ρ, κ]

end GlobalTheory.CechH1Span
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentityTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefThetaNZ

section Darboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_zero {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (h : UA σ Wd.J) :
    M.I om 0 h = 0 := by
  simp [Model.I, theta, GlobalTheory.WeilM.thetaSum]

theorem I_smul' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ Wd.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    MeasureTheory.integral_const_mul]

theorem I_add' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd)
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} {h : UA σ Wd.J}
    (hΦ : MeasureTheory.IntegrableOn (fun g => theta om Φ g h) M.dom M.μ)
    (hΨ : MeasureTheory.IntegrableOn (fun g => theta om Ψ g h) M.dom M.μ)
    (hs : ∀ g, om (g, h) Φ ∈ GlobalTheory.WeilM.schA F _ ∧ om (g, h) Ψ ∈ GlobalTheory.WeilM.schA F _) :
    M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← MeasureTheory.integral_add hΦ hΨ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun g => ?_)
  show GlobalTheory.WeilM.thetaSum F (om (g, h) (Φ + Ψ)) = GlobalTheory.WeilM.thetaSum F (om (g, h) Φ) + GlobalTheory.WeilM.thetaSum F (om (g, h) Ψ)
  rw [map_add, GlobalTheory.WeilM.thetaSum_add F (hs g).1 (hs g).2]

theorem exists_algD_ne (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (hDec : Decay B G om om')
    {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hne : G.M'.I om' Φ' ≠ 0) :
    ∃ ΦD ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, G.M'.I om' ΦD ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  clear hne
  funext h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), om' x Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) :=
    hPair.weil.isUSplitting.pres
  have hdense := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ hPair
  have hsch : ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, Ψ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) := by
    intro Ψ hΨ
    refine (Submodule.span_le.2 ?_) hΨ
    rintro _ ⟨f, φ, hSB, hvac, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
    filter_upwards [hvac, hT.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  show G.M'.I om' Φ' h = 0
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    have hc := GlobalTheory.T.restricted_product_decay_vacuum hP F E σ B a a' G X om om' hT hDec φ hSB hvac hv₁ h
    have hz : ∀ P ∈ (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))), G.M'.I om' (pure P φ) h = 0 := fun P hP' =>
      congrFun (hall _ (Submodule.subset_span ⟨P, φ, hP', hSB, hvac, rfl⟩)) h
    have hcl : IsClosed {f : SInf F (Fin a' × Fin (a + a')) | G.M'.I om' (pure f φ) h = 0} := isClosed_eq hc continuous_const
    have hsub := hcl.closure_subset_iff.2 hz
    rw [hdense.closure_eq] at hsub
    exact hsub (Set.mem_univ f)
  | zero => exact I_zero _ _ h
  | add x y hx hy ihx ihy =>
    rw [I_add' G.M' om' ((hDec.2 x hx).2.1 h) ((hDec.2 y hy).2.1 h) (fun g => ⟨hpres _ _ (hsch x hx), hpres _ _ (hsch y hy)⟩),
      ihx, ihy, add_zero]
  | smul c x hx ihx => rw [I_smul', ihx, mul_zero]

end Darboux

end GlobalTheory.DefThetaNZ

namespace GlobalTheory.DefThetaNZ

open scoped Matrix

theorem exists_algF_thetaInt_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  intro hP hK hL D ψ θ _hψ hθ W W₁ X A A₁ B α β hT _hdef ν₁ 𝓕₁ hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨⟨Φ', hΦ'So, hne⟩, -⟩, -⟩ := hK' R Rf hR
  obtain ⟨ΦD, hΦD, hneD⟩ := exists_algD_ne hP hTD hDec hΦ'So hne
  obtain ⟨Φ, hΦ, hDat⟩ := hO.algB' ΦD hΦD
  refine ⟨Φ, hΦ, fun h0 => ?_⟩
  obtain ⟨h', hh'⟩ := Function.ne_iff.1 hneD
  obtain ⟨h, rfl⟩ := GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective D X e hO.JX h'
  have := GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) ΦD Φ
    hO.measW₁ hO.domW₁ (hO.theta_eq_B hDat) h
  rw [h0] at this
  exact hh' this.symm

end GlobalTheory.DefThetaNZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroDeRhamAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section Helpers

variable {R : Type} [CommRing R]

theorem cup_self_eq_zero_of_wedgeO' {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F)
    (x : CatCoh.H1 F) : cup F x x = 0 := by
  obtain ⟨e, he⟩ := hW
  rw [← he]
  have : exteriorPower.ιMulti R 2 ![x, x] = 0 :=
    AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
  rw [this, map_zero]

theorem fn_cupZZ_self_exact {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F) (c : cechDeRhamTotalCocyclesOne F) :
    ∃ f, d1 F f = (cupZZ F c c).1.1 := by
  have h := cup_self_eq_zero_of_wedgeO' hW (H1.mk F (cechDeRhamTotalCocyclesOne.fn F c))
  rw [cup_mk, H2.mk_eq_zero] at h
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf⟩

variable {Y A : Over (Sp R)}

theorem pH2_cupHH_over (f : Y ⟶ A) (a b : HH1 A.hom) :
    deRhamH2Pullback f (cupHH A.hom a b) = cupHH Y.hom (deRhamH1Pullback f a) (deRhamH1Pullback f b) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.1 a b

theorem toHO1_pH1_over (f : Y ⟶ A) (a : HH1 A.hom) : toHO1 Y.hom (deRhamH1Pullback f a) = pO1 f (toHO1 A.hom a) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.2 a

theorem pH1_clAll_over (f : Y ⟶ A) (hc : Closed1 (OAff A.hom) = ⊤) (hc' : Closed1 (OAff Y.hom) = ⊤)
    (w : GlobForm A.hom) : deRhamH1Pullback f (clAll (OAff A.hom) hc w) = clAll (OAff Y.hom) hc' (pF f w) :=
  GlobalTheory.T.pull_closed_form_class R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) hc hc' w

end Helpers

section Wsum

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem wsum_finAppend {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem wsum_neg_first {n : ℕ} (u v : Fin n → Glob1 F) : wsum F (fun k ↦ -u k) v = -wsum F u v := by
  funext T
  simp only [wsum, Submodule.coe_neg, Pi.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]

theorem wsum_eq_add_of_cupSum_eq (hc : Closed1 F = ⊤) (hsur : Function.Surjective (toO F)) {m : ℕ}
    (u₁ v₁ u₂ v₂ u₃ v₃ : Fin m → Glob1 F)
    (h : ∑ k, cupHyp F (clAll F hc (u₁ k)) (clAll F hc (v₁ k)) =
      ∑ k, cupHyp F (clAll F hc (u₂ k)) (clAll F hc (v₂ k)) + ∑ k, cupHyp F (clAll F hc (u₃ k)) (clAll F hc (v₃ k))) :
    wsum F u₁ v₁ = wsum F u₂ v₂ + wsum F u₃ v₃ := by
  have h2 : ∑ k, cupHyp F (clAll F hc (Fin.append (Fin.append u₁ (fun k ↦ -u₂ k)) (fun k ↦ -u₃ k) k))
      (clAll F hc (Fin.append (Fin.append v₁ v₂) v₃ k)) = 0 := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
    rw [h]
    abel
  have h3 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hsur _ _ _).1 h2
  rw [wsum_finAppend, wsum_finAppend, wsum_neg_first, wsum_neg_first] at h3
  rw [← sub_eq_zero, ← h3]
  abel

end Wsum

theorem cupHH_self_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ a : HH1 A.hom, cupHH A.hom a a = 0 := by
  intro R _ A _ g hA hs a
  have hb := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hb2 := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have hc2 := GlobalTheory.T.abelianScheme_globalOneForms_closed R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hsur := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs
  have hsur2 := GlobalTheory.T.de_rham_to_structure_h1_surjective R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hW := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).2.1
  have hP : ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hs).2
  have hPF : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  have hax := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  have anti := GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm R _ (OAff (A ⊗ A).hom)

  have hprim : deRhamH2Pullback μ[A] (cupHH A.hom a a) =
      deRhamH2Pullback (fst A A) (cupHH A.hom a a) + deRhamH2Pullback (snd A A) (cupHH A.hom a a) := by
    rw [pH2_cupHH_over, pH2_cupHH_over, pH2_cupHH_over, hP a]
    have h := anti (deRhamH1Pullback (fst A A) a) (deRhamH1Pullback (snd A A) a)
    simp only [map_add, LinearMap.add_apply]
    linear_combination (norm := module) h

  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective _ a
  obtain ⟨n, a', w, hz⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R _ (OAff A.hom) hb.1 hb.2.1 hc hsur (cupZZ _ c c) (fn_cupZZ_self_exact hW c)
  rw [← cupHyp_mk] at hz
  change cupHH A.hom _ _ = _ at hz
  set z := cupHH A.hom (Hyp1.mk _ c) (Hyp1.mk _ c)
  clear_value z

  have hcross : ∑ k, (cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (fst A A) (a' k)) (clAll _ hc2 (pF (snd A A) (w k))) +
      cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (snd A A) (a' k)) (clAll _ hc2 (pF (fst A A) (w k)))) = 0 := by
    have h := hprim
    rw [hz] at h
    simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2, hP, hPF, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib] at h
    rw [Finset.sum_add_distrib]
    linear_combination (norm := module) h

  have hk : ∀ l : Glob1 (OAff A.hom) →ₗ[R] R, ∑ k, l (w k) • toO (OAff A.hom) (a' k) = 0 := by
    intro l
    have h2 : ∑ k, cupHH (A ⊗ A).hom
        (Fin.append (fun k ↦ deRhamH1Pullback (fst A A) (a' k)) (fun k ↦ deRhamH1Pullback (snd A A) (a' k)) k)
        (clAll _ hc2 (Fin.append (fun k ↦ pF (snd A A) (w k)) (fun k ↦ pF (fst A A) (w k)) k)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.sum_add_distrib]
      exact hcross
    have h3 := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R _ _ hb2.1 hb2.2.1 hc2 hsur2 (n + n) _ _ h2
      (l ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
    rw [Fin.sum_univ_add] at h3
    simp only [Fin.append_left, Fin.append_right, LinearMap.comp_apply, (hax.2.1 _).2.2.2.1,
      (hax.2.1 _).2.2.2.2.1, map_zero, zero_smul, Finset.sum_const_zero, add_zero] at h3
    have h4 := congrArg (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) h3
    simp only [map_sum, map_smul, map_zero] at h4
    simpa only [toHO1_pH1_over, (hax.1 _).1] using h4

  obtain ⟨m, ⟨Φ⟩⟩ := hb.1
  obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R _ (OAff A.hom) hb.2.1 m Φ
  have hu : ∀ i, ∃ u : Glob1 (OAff A.hom), clAll _ hc u = ∑ k, L i (w k) • a' k := by
    intro i
    have hm : ∑ k, L i (w k) • a' k ∈ Fil1 (OAff A.hom) := by
      rw [Fil1, LinearMap.mem_ker, map_sum]
      simpa only [map_smul] using hk (L i)
    rw [Fil1_eq_range] at hm
    obtain ⟨ω, hω⟩ := hm
    refine ⟨ω.1, ?_⟩
    rw [← hω]
    rfl
  choose u hu using hu
  have hz2 : z = ∑ i, cupHyp (OAff A.hom) (clAll _ hc (u i)) (clAll _ hc (Φ.w i)) := by
    rw [hz]
    simp only [hu]
    conv_lhs => enter [2, k]; rw [hL (w k)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_comm

  have hwp : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (Φ.w k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (Φ.w k)) +
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (Φ.w k)) := by
    have h := hprim
    rw [hz2] at h
    simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2] at h
    exact wsum_eq_add_of_cupSum_eq _ hc2 hsur2 _ _ _ _ _ _ h
  have hw0 := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hs m u Φ.w hwp
  rw [hz2]
  exact (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R _ _ hc hsur m u Φ.w).2 hw0

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameOffClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 4000000 in

theorem exists_carried_frame_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  have hβc : IsClosedMap β.base := by
    haveI : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    haveI : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip inferInstance
    exact β.isClosedMap
  obtain ⟨V, hyV, s, hs, hun, hcar⟩ := GlobalTheory.T.exists_carried_section_off_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact y hy
  obtain ⟨V', hyV', -, T, hT, htr⟩ := GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre _ _ β hβc U'.LG.L U'.LG.isLB V s hs y hyV hun
  refine ⟨V', hyV', T, hT, ?_⟩
  intro σ h bc hbc hP hPO
  refine (hcar σ).elim fun h₀ hc => hc.elim fun bc₀ hc => ?_
  refine hc.2.elim fun hP₀ hc' => ?_
  have hF₀ := htr _ _ hc'.2
  have e : bc₀.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := hc.1.trans hbc.symm
  have s₁ := Classical.choose_spec hP.lg
  have s₀ := Classical.choose_spec hP₀.lg
  refine s₁.2.elim fun he₁ m₁ => s₀.2.elim fun he₀ m₀ => ?_
  have hg := GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits R' D' A' G' hS' U' (specOf (Gal.hom σ)) _ _ e he₀ he₁ _ _ s₀.1 s₁.1 m₀.1 m₁.1
  intro z j k hz hfz hzk hfzj
  have h1 := hF₀ z j k hz (by rw [e]; exact hfz) hzk (by rw [e]; exact hfzj)
  rw [hg z j k hzk (by rw [e]; exact hfzj)] at h1
  rw [e] at h1
  exact h1

end GlobalTheory.Mum
end

