import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

theorem alg_eq {R F : Type} [CommRing R] [IsDomain R] [Field F] (i₁ i₂ : Algebra (FractionRing R) F)
    (h : ∀ r, @algebraMap _ _ _ _ i₁ (algebraMap R (FractionRing R) r) =
      @algebraMap _ _ _ _ i₂ (algebraMap R (FractionRing R) r)) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro x
  have e := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := FractionRing R)
    (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext h)
  exact RingHom.congr_fun e x

theorem qk_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {q q' : QkPt D F k} (hy : q.y = q'.y) (hg : q.g = q'.g) : q = q' := by
  cases q; cases q'; cases hy; cases hg; rfl

theorem tor_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {τ : Multiplicative D.X →* Fˣ} {g : GtPtF D F} (h : GlobalTheory.UT.IsTor τ g) :
    g = GlobalTheory.TorusExt.torusPt D F (Additive.ofMul τ) :=
  (GlobalTheory.TorusExt.isTorusPtF_iff_eq g τ).1 ((GlobalTheory.UT.isTor_iff τ g).1 h)

theorem one_le_of_isUnit {R : Type} [CommRing R] [IsDomain R] {k : ℕ} (hk : IsUnit (k : R)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hk
  · exact h

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem tors_fun (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {k : ℕ} (hk : IsUnit (k : R)) :
    ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧
      (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') := by
  haveI := hR.2
  obtain ⟨f, ⟨h1, -, h3, h4, -⟩, -⟩ :=
    GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR.1 D A G hG U F k (one_le_of_isUnit hk)
  exact ⟨f, h1, h3, h4⟩

theorem push {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    (U : Unif (maximalIdeal R) D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ e : (TFK (R := R) F ⟶ A.A) ≃* (Over.mk (jFK (R := R) F ≫ jK R) ⟶ G), ∀ x, (e x).left = x.left ≫ genMap U :=
  GlobalTheory.LiePull.exists_pushEquiv (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre) (TFK (R := R) F) _ rfl

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem torMatch_id (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) :
    TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, -, -⟩ := tors_fun hR hG U F hk
  have e : τ = τ' := MonoidHom.ext fun x => hρ (Multiplicative.toAdd x)
  subst e
  have hqq : q = q' := qk_eq (hy.trans hy'.symm) ((tor_eq hτ).trans (tor_eq hτ').symm)
  subst hqq
  rw [(h1 q a).1 hq, (h1 q a').1 hq', Category.comp_id]

theorem torMatch_one (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') :
    TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ _ _ hq _
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  have e : τ = 1 := MonoidHom.ext fun x => by
    rw [MonoidHom.one_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.zero_apply, ofAdd_zero, map_one]
  subst e
  have hg : q.g = 0 := by rw [tor_eq hτ, ofMul_one, map_zero]
  have hadd : QkAdd q q q := ⟨q, by rw [hy, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (by rw [hg, add_zero]),
    (h3 q q).1 rfl⟩
  have ha : a = 1 := by
    rw [(h1 q a).1 hq]
    exact mul_eq_left.1 (h4 q q q hadd).symm
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have key : eU a = eU' a' ≫ (1 : G' ⟶ G) := by rw [comp_one, ha, map_one]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

theorem torMatch_mul (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') (p p' : G' ⟶ G) (ρ ρ' : D.toPre.X →+ D'.toPre.X)
    (hp : TorMatch U U' (RingHom.id R) p.left ρ) (hp' : TorMatch U U' (RingHom.id R) p'.left ρ') :
    TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' hτk hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
  let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
  have pw : ∀ σ : D.toPre.X →+ D'.toPre.X, (τ'.comp (AddMonoidHom.toMultiplicative σ)) ^ k = 1 := fun σ =>
    MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hτk, MonoidHom.one_apply,
        MonoidHom.one_apply]
  obtain ⟨q₁, hy₁, hτ₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₁ (pw ρ)
  obtain ⟨q₂, hy₂, hτ₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₂ (pw ρ')
  have e₁ := hp F hF k hk τ₁ τ' q₁ q' (f q₁) a' hτk (fun _ => rfl) hy₁ hτ₁ hy' hτ' ((h1 q₁ _).2 rfl) hq'
  have e₂ := hp' F hF k hk τ₂ τ' q₂ q' (f q₂) a' hτk (fun _ => rfl) hy₂ hτ₂ hy' hτ' ((h1 q₂ _).2 rfl) hq'
  have hτe : τ = τ₁ * τ₂ := MonoidHom.ext fun x => by
    rw [MonoidHom.mul_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    rfl
  have hg : q.g = q₁.g + q₂.g := by
    rw [tor_eq hτ, tor_eq hτ₁, tor_eq hτ₂, hτe, ofMul_mul, map_add]
  have hadd : QkAdd q₁ q₂ q := ⟨q, by rw [hy, hy₁, hy₂, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 hg,
    (h3 q q).1 rfl⟩
  have ha : a = f q₁ * f q₂ := by rw [(h1 q a).1 hq]; exact h4 q₁ q₂ q hadd
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have k₁ : eU (f q₁) = eU' a' ≫ p := Over.OverMorphism.ext (by rw [heU, e₁, Over.comp_left, heU', Category.assoc])
  have k₂ : eU (f q₂) = eU' a' ≫ p' := Over.OverMorphism.ext (by rw [heU, e₂, Over.comp_left, heU', Category.assoc])
  have key : eU a = eU' a' ≫ (p * p') := by rw [comp_mul, ha, map_mul, k₁, k₂]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8

open TorMatchLaws in

theorem torMatch_id_one_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G'), TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) ∧ TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 ∧ ∀ (p p' : G' ⟶ G) ρ ρ', TorMatch U U' (RingHom.id R) p.left ρ → TorMatch U U' (RingHom.id R) p'.left ρ' → TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ _ D' A' U'
  exact ⟨torMatch_id hR hG U, torMatch_one hR hG U U', fun p p' ρ ρ' hp hp' => torMatch_mul hR hG U U' p p' ρ ρ' hp hp'⟩

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagPointTangentDualNumber
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigLetters

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

def tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : TanM x0 t.G :=
  mkT (ovT hv) (smT_zero_ovT hv)

theorem tv_tvG {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tv (tvG hv) = ovT hv := rfl

theorem tvG_tv (n : TanM x0 t.G) : tvG (isTanAtG_of (t := t) (x0 := x0) (tv n) (tv_mem n)) = n :=
  tanM_ext (Over.OverMorphism.ext rfl)

theorem tv_sumG {κ : Type} (s : Finset κ) (f : κ → TanM x0 t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finset_prod]

theorem combG_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hu : ∀ i, IsTanAtG t x0 (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x0 w) :
    IsCombAtG t x0 u cf w ↔ tvG hw = ∑ i, cf i • tvG (hu i) := by
  have e : IsCombAtG t x0 u cf w ↔ (combT x0 (fun i => ovT (hu i)) cf).left = w :=
    isCombAtG_iff t x0 (fun i => ovT (hu i)) cf w
  rw [e]
  constructor
  · intro h
    apply tanM_ext
    rw [tv_sumG, tv_tvG]
    apply Over.OverMorphism.ext
    exact h.symm
  · intro h
    have h3 : ovT hw = combT x0 (fun i => ovT (hu i)) cf := by
      rw [← tv_tvG hw, h, tv_sumG]
      rfl
    exact (congrArg (fun V => Over.Hom.left V) h3).symm

end Tan

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)

theorem letters_nodup : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map (fun i j h => ?_), ?_⟩
  · simpa using h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hxa hxb
    simp only [List.mem_map, List.mem_finRange, true_and] at hxa hxb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, hj⟩ := hxb
    have := congrArg Sigma.fst hj
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective this.symm)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  unfold letters
  refine List.mem_flatMap.2 ⟨Fintype.equivFin (E →+* ℂ) τ, List.mem_finRange _, ?_⟩
  generalize hσ : (Fintype.equivFin (E →+* ℂ)).symm (Fintype.equivFin (E →+* ℂ) τ) = σ
  obtain rfl : σ = τ := by rw [← hσ, Equiv.symm_apply_apply]
  exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

end Letters

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {Ω : Type} [Field Ω] [Algebra c.F Ω] (y : FlagPt Z Ω) (hA : algebraMap c.F Ω = y.fK)

include hA in
theorem eig_iffG (τ : E →+* ℂ) {w : Sp (DualNumber Ω) ⟶ Z.t.G.left} (hw : IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w) :
    (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (y.fK (embF c τ (a : E)))) ≫ w) ↔
      IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (tvG hw) := by
  rw [← hA]
  refine forall_congr' fun a => ⟨fun h => tanM_ext ?_, fun h => ?_⟩
  · apply Over.OverMorphism.ext
    exact h
  · have := congrArg (fun V => (tv V).left) h
    exact this

include hA in
theorem eig_coordsG (τ : E →+* ℂ) (n : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G)
    (hn : IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → Ω, n = ∑ i, a i • tvG (y.tan τ i) := by
  have hw := isTanAtG_of (t := Z.t) (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (tv n) (tv_mem n)
  have heig := (eig_iffG y hA τ hw).2 ((tvG_tv n).symm ▸ hn)
  obtain ⟨a, ha, hu⟩ := y.basis τ _ hw heig
  refine ⟨a, ?_, fun b hb => hu b ?_⟩
  · rw [← tvG_tv n]
    exact (combG_iff (y.u τ) (y.tan τ) a hw).1 ha
  · refine (combG_iff (y.u τ) (y.tan τ) b hw).2 ?_
    rw [tvG_tv n]
    exact hb

theorem eig_combG {x : Sp Ω ⟶ Z.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Z.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (v i)) (a : Fin m → Ω) :
    IsEigV (actR (x0 := x) (S := Ω) Z.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

def fullG : Letter Dw → TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G := fun k => tvG (y.tan k.1 k.2)

include hA in
theorem fullG_eig (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act) (embK c τ) (fullG y ⟨τ, i⟩) :=
  (eig_iffG y hA τ (y.tan τ i)).1 (y.eig τ i)

include hA in
theorem fullG_basis (m : TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) :
    ∃! a : Letter Dw → Ω, m = ∑ k, a k • fullG y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.y ≫ GlobalTheory.Toroidal.genι Z) (S := Ω) Z.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End Ω (TanM (y.y ≫ GlobalTheory.Toroidal.genι Z) Z.t.G) => e m)
      (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coordsG y hA τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : Letter Dw, a k.1 k.2 • fullG y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : Letter Dw, b k • fullG y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullG y ⟨τ, i⟩)
      (fun τ => eig_combG τ _ (fun i => fullG_eig y hA τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end Flag

theorem letters_basis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {Ω : Type} [Field Ω] (y : GlobalTheory.ShFam.Pad.FlagPt Z Ω) (w : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber Ω) ⟶ Z.t.G.left), Formalism.L2.Pj.IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w → ∃! a : Fin (GlobalTheory.ShFam.Pad.letters Dw).length → Ω, Formalism.L2.Pj.IsCombAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) (fun k => y.u ((GlobalTheory.ShFam.Pad.letters Dw).get k).1 ((GlobalTheory.ShFam.Pad.letters Dw).get k).2) a w := by
  intro E _ _ _ H Dw l Xo c O _ β Z Ω _ y w hw
  classical
  letI : Algebra c.F Ω := y.fK.toAlgebra
  set L := GlobalTheory.ShFam.Pad.letters Dw with hL
  let e : Fin L.length ≃ Letter Dw := (letters_nodup Dw).getEquivOfForallMemList _ (mem_letters Dw)
  have he : ∀ k, e k = L.get k := fun k => rfl
  have hc : ∀ a : Fin L.length → Ω, Formalism.L2.Pj.IsCombAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z)
      (fun k => y.u (L.get k).1 (L.get k).2) a w ↔ tvG hw = ∑ k, a k • fullG y (e k) := fun a =>
    combG_iff (fun k => y.u (L.get k).1 (L.get k).2) (fun k => y.tan _ _) a hw
  obtain ⟨b, hb, hbu⟩ := fullG_basis y rfl (tvG hw)
  refine ⟨fun k => b (e k), (hc _).2 ?_, fun a ha => ?_⟩
  · rw [hb]
    exact (Equiv.sum_comp e (fun x => b x • fullG y x)).symm
  · have h1 := (hc a).1 ha
    have h2 : tvG hw = ∑ x, a (e.symm x) • fullG y x := by
      rw [h1, ← Equiv.sum_comp e]
      simp
    have := hbu _ h2
    funext k
    have := congrFun this (e k)
    simpa using this

end GlobalTheory.EigLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalSquares

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_div {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    {k : ℕ} (l N : ℕ) (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) :
    ∃ q : QkPt D.toPre (Kb R) N, q.y = p.y ∧ l • q.g = p.g := by
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_nsmul_eq (F := Kb R) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1.1)
    (n := l) (by omega) p.g
  refine ⟨GlobalTheory.TorusExt.qkMk D.tau_bimult p.y g ?_, rfl, hg⟩
  rw [hN, mul_nsmul', hg]
  exact GlobalTheory.TorusExt.qk_nsmul D.tau_bimult p

theorem qkExt_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') {k N : ℕ}
    (l : ℕ) {p : QkPt D F k} {p' : QkPt D F' k} {q : QkPt D F N} (hp : QkExt σ.toRingHom p p') (hy : q.y = p.y)
    (hg : l • q.g = p.g) : ∃ q' : QkPt D F' N, QkExt σ.toRingHom q q' ∧ q'.y = p'.y ∧ l • q'.g = p'.g := by
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext σ.commutes
  refine ⟨GlobalTheory.TorusExt.qkExt hB σ.toRingHom hσ q, (GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).2 rfl, ?_, ?_⟩
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    exact hy
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    show l • GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ q.g = GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ p.g
    rw [← map_nsmul, hg]

theorem pow_left_of_comp {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (x y : TFK (R := R) (Kb R) ⟶ A.A) (h : y.left = spMap σ.toRingHom ≫ x.left)
    (l : ℕ) : (y ^ l).left = spMap σ.toRingHom ≫ (x ^ l).left := by
  let s : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap σ.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes))
  have hy : y = s ≫ x := Over.OverMorphism.ext h
  have hp : ∀ m : ℕ, s ≫ x ^ m = (s ≫ x) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [hy, ← hp]
  rfl

theorem compPow {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (m : ℕ) :
    (ρ ≫ x) ^ m = ρ ≫ x ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem lab_level {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hO : OneTrait D.toPre A lab) (k l N : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) N) (hy : q.y = p.y)
    (hg : GtPtF.IsNsmul l q.g p.g) : (lab k p).left = ((lab N q) ^ l).left := by
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hl
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := (GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k l N hk hl hN
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab N q))).2
    (by show hD.xe.symm p.y = hD.xe.symm q.y; rw [hy])
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g) =
        l • GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g)
      rw [(GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg, map_nsmul, map_nsmul])) (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₁).trans ((hf _ _).1 h₂).symm
  have hs : s ≫ lab k p = s ≫ lab N q ^ l := by
    have := congrArg e hx
    rw [e.apply_symm_apply, map_pow, e.apply_symm_apply] at this
    rw [this, compPow]
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs)

end GlobalTheory.Mum.GalSquares

open GlobalTheory.Mum.GalSquares in

theorem GlobalTheory.Mum.galEqN_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime →
    Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' →
        (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  intro R _ _ _ hR n hn _ _ D A lab hO ⟨i₀, H⟩ σ j p p' hpp'
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (Kb R)
  have hi : i₀ ≤ max i₀ j := le_max_left _ _
  have hj : j ≤ max i₀ j := le_max_right _ _
  have hN : (n ^ max i₀ j) ^ 2 = n ^ j * n ^ (2 * max i₀ j - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hl : 1 ≤ n ^ (2 * max i₀ j - j) := Nat.one_le_pow _ _ hn.pos
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  obtain ⟨q, hqy, hqg⟩ := exists_div hR D _ _ hl hN p
  obtain ⟨q', hq', hq'y, hq'g⟩ := qkExt_nsmul D.toPre D.tau_bimult σ _ hpp' hqy hqg
  have e₁ := lab_level D A lab hO _ _ _ hk hl hN p q hqy ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hqg.symm)
  have e₂ := lab_level D A lab hO _ _ _ hk hl hN p' q' hq'y ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hq'g.symm)
  rw [e₂, pow_left_of_comp σ _ _ (H _ hi σ q q' hq'), ← e₁]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_geometricFibres_of_descended_group : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  first | exact @GlobalTheory.Mum.torusExtension_of_descended | exact GlobalTheory.Mum.torusExtension_of_descended | (intros; apply GlobalTheory.Mum.torusExtension_of_descended <;> assumption)
end

