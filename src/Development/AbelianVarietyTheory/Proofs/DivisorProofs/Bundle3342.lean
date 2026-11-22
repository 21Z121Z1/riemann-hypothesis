import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantFourierPartsBoundedClassMinima
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.CNorm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem transport (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N)
    (c' : T' →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ T'), c ⟨t, h1⟩ = c' ⟨t, h2⟩) :
    S.proj T c = S.proj T' c' ∧ ∀ k', ∃ k, S.FF T c k = S.FF T' c' k' := by
  subst h
  obtain rfl : c = c' := AddMonoidHom.ext fun t => hc t t.2 t.2
  exact ⟨rfl, fun k' => ⟨k', rfl⟩⟩

theorem mem_supI_iff_norm {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) (a : S.Gam) :
    a ∈ S.supI M x ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = τ.δ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : ∀ b ∈ S.R, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 (hO.le hb) _ (hc.2 ⟨w, rfl⟩)
  have hOx : ∀ b ∈ M.O x, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 w) hb
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have key : ∀ a₁ ∈ S.supI M x, ∀ a', ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ =
      ‖M.val (gPt p ≫ y) (S.th a' / S.th a₁)‖ * ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ := by
    intro a₁ h₁ a'
    rw [hval, hval, ← norm_mul, ← RatModel.val_mul hsp (hOx _ (h₁.2 a')) (hR _ (S.th_mem a₁)),
      div_mul_cancel₀ _ h₁.1]
  have hmax : ∀ a₁ ∈ S.supI M x, ‖y₀ ⟨S.th a₁, S.th_mem a₁⟩‖ = τ.δ := by
    intro a₁ h₁
    refine IsGreatest.unique (s := Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) ⟨⟨a₁, rfl⟩, ?_⟩ τ.δ_max
    rintro _ ⟨a', rfl⟩
    show ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ ≤ _
    rw [key a₁ h₁ a']
    exact mul_le_of_le_one_left (norm_nonneg _) (hc.norm_val_le_one (h₁.2 a'))
  refine ⟨hmax a, fun h => ?_⟩
  obtain ⟨a₁, h₁⟩ := hO.div x
  have e := key a₁ h₁ a
  rw [h, hmax a₁ h₁] at e
  have h1 : ‖M.val (gPt p ≫ y) (S.th a / S.th a₁)‖ = 1 :=
    mul_right_cancel₀ τ.δ_pos.ne' (e.symm.trans (_root_.one_mul _).symm)
  exact (RatModel.Div.div_iff_isUnit h₁ a).2 ((RatModel.norm_val_eq_one_iff hc.1 (h₁.2 a)).1 h1)

theorem HH_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) (τ : S.Test p y₀) : S.HH M x = τ.yy.ker := by
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext a
  exact mem_supI_iff_norm hO hc hat τ a

theorem norm_val_div {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {x : M.Z}
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₀ x y) {y₀ : S.R →+* PadicAlgCl p}
    (hat : S.At M y y₀) {F : Ω} (hF : F ∈ S.R) {a : S.Gam} (ha : S.th a ≠ 0) :
    ‖M.val (gPt p ≫ y) (F / S.th a)‖ = ‖y₀ ⟨F, hF⟩‖ / ‖y₀ ⟨S.th a, S.th_mem a⟩‖ := by
  set w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hsp : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hU : ∀ b ∈ M.ringOn U₀, b ∈ M.O ((gPt p ≫ y) w) := fun b hb =>
    RatModel.mem_ringOn.1 hb _ (hc.2 ⟨w, rfl⟩)
  have hth := hU _ (hO.le (S.th_mem a))
  have hinv := hU _ (hO.th_unit a ha)
  have hval : ∀ b (hb : b ∈ S.R), y₀ ⟨b, hb⟩ = M.val (gPt p ≫ y) b := fun b hb => hat ⟨b, hb⟩
  have e1 : M.val (gPt p ≫ y) (S.th a) * M.val (gPt p ≫ y) (S.th a)⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hth hinv, mul_inv_cancel₀ ha, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (hU _ (hO.le hF)) hinv, hval, hval, norm_mul, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right e1, norm_inv]

theorem norm_FF_le {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    {β : τ.X} (hβ : ∀ v0, τ.q β ≤ τ.q (β + S.N • v0)) {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker)
    (c : T →+ ZMod S.N) (hc : ∀ t (h1 : t ∈ T) (h2 : t ∈ S.perp τ.yy.ker), c ⟨t, h1⟩ = τ.wt β ⟨t, h2⟩)
    (κ : S.J × (T → ZMod ((S.r * S.N) ^ 2))) :
    ‖y₀ ⟨S.FF T c κ, S.FF_mem T c κ⟩‖ ≤ τ.δ * Real.exp (-(τ.q β / S.N)) := by
  have hproj := (transport S hT c (τ.wt β) hc).1
  have := Fintype.ofFinite T
  rw [S.map_FF y₀ T c κ]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos τ.δ_pos (Real.exp_pos _)).le
    fun t _ => ?_
  rw [norm_mul, norm_pow, S.norm_ζ, one_pow, _root_.one_mul, hproj]
  exact τ.le β hβ t (τ.perp_ker_le_ker (hT ▸ t.2)) κ.1

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → S.IsoFree (S.TT M x) ∧ ∀ α₀ : D.toPre.X, ∃ c' : S.TT M x →+ ZMod S.N, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ x₀ ∈ S.supI M x, (∀ κ, ∃ α s, CongMod S.N α α₀ ∧ PsiCoord D.toPre α s ∧ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖) ∧ ∃ κ, ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, H⟩ := GlobalTheory.T.complete_local_base_at_closed_point_group o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  have hO := hAdm.1
  obtain ⟨p₁, hp₁, y₁, hc₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hcomp₁, -⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hCpl p₁ y₁ hc₁.1
  obtain ⟨y₀₁, hat₁, -⟩ := S.exists_at_of_cen M hO.le hc₁
  obtain ⟨τ₁, ε₁, -, hlab₁⟩ := H p₁ y₁ (i.comp ev₀) hc₁ hcomp₁ y₀₁ hat₁
  have hTT₁ : S.TT M x = S.perp τ₁.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc₁ hat₁ τ₁]
  refine ⟨by rw [hTT₁]; exact τ₁.isoFree, fun α₀ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := τ₁.yy_onto (QuotientAddGroup.mk (ε₁ α₀))
  have hya₀ : yy a₀ = QuotientAddGroup.mk α₀ := (hlab₁ a₀ α₀).2 ha₀
  let c' : S.TT M x →+ ZMod S.N :=
    { toFun := fun t => ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) a₀)
      map_zero' := by simp
      map_add' := fun t t' => by simp [eStd_add_left] }
  refine ⟨c', ?_⟩
  intro p _ y ev hc hcomp x₀ hx₀
  obtain ⟨y₀, hat, -⟩ := S.exists_at_of_cen M hO.le hc
  obtain ⟨τ, ε, hnorm, hlab⟩ := H p y ev hc hcomp y₀ hat
  have hTT : S.TT M x = S.perp τ.yy.ker := by rw [ThetaSys.TT, HH_eq hO hc hat τ]
  obtain ⟨v, hv⟩ := τ.exists_shortest (ε α₀)
  have hwt : ∀ t (h1 : t ∈ S.TT M x) (h2 : t ∈ S.perp τ.yy.ker),
      c' ⟨t, h1⟩ = τ.wt (ε α₀ + S.N • v) ⟨t, h2⟩ := by
    intro t h1 h2
    have hτa : τ.yy a₀ = QuotientAddGroup.mk (ε α₀) := (hlab a₀ α₀).1 hya₀
    rw [map_add, τ.wt_nsmul, add_zero, τ.wt_eq a₀ (ε α₀) hτa]
    rfl
  have hqβ : ∀ α', CongMod S.N α' α₀ → τ.q (ε α₀ + S.N • v) ≤ τ.q (ε α') := by
    rintro α' ⟨w', rfl⟩
    have e : ε (α₀ + S.N • w') = ε α₀ + S.N • v + S.N • (ε w' - v) := by
      rw [map_add, map_nsmul, smul_sub]
      abel
    rw [e]
    exact hv _
  have hα : CongMod S.N (ε.symm (ε α₀ + S.N • v)) α₀ :=
    ⟨ε.symm v, by rw [map_add, map_nsmul, AddEquiv.symm_apply_apply]⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre (ε.symm (ε α₀ + S.N • v))).2
    (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  have hsn : ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [hnorm _ s hs, AddEquiv.apply_symm_apply]
  have hN : (S.N : ℝ) ≠ 0 := by have := S.N_ge; positivity
  have hexp : Real.exp (-(τ.q (ε α₀ + S.N • v) / S.N)) ^ S.N = Real.exp (-τ.q (ε α₀ + S.N • v)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hδ : ‖y₀ ⟨S.th x₀, S.th_mem x₀⟩‖ = τ.δ := (mem_supI_iff_norm hO hc hat τ x₀).1 hx₀
  refine ⟨fun κ => ⟨_, s, hα, hs, ?_⟩, ?_⟩
  · rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ, hsn, ← hexp]
    refine pow_le_pow_left₀ (div_nonneg (norm_nonneg _) τ.δ_pos.le) ?_ _
    rw [div_le_iff₀ τ.δ_pos, mul_comm]
    exact norm_FF_le τ hv hTT c' hwt κ
  · obtain ⟨k, hk, hkeq⟩ := τ.eq _ hv
    obtain ⟨κ, hκ⟩ := (transport S hTT c' _ hwt).2 k
    refine ⟨κ, fun α' s' hα' hs' => ?_⟩
    have e : ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ^ S.N =
        Real.exp (-τ.q (ε α₀ + S.N • v)) := by
      rw [norm_val_div hO hc hat (S.FF_mem _ c' κ) hx₀.1, hδ,
        show (⟨S.FF (S.TT M x) c' κ, S.FF_mem _ c' κ⟩ : S.R) = ⟨_, hk⟩ from Subtype.ext hκ, hkeq,
        mul_div_cancel_left₀ _ τ.δ_pos.ne', hexp]
    rw [e, hnorm α' s' hs']
    exact Real.exp_le_exp.2 (neg_le_neg (hqβ α' hα'))

end GlobalTheory.Poinc.CNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCoordinatesSectionExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : Γ(X, U)) :
    resG X h₂ (resG X h₁ f) = resG X (h₂.trans h₁) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem chart_sec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G))
    (hn : Geo.Tor.IsNormalScheme M.Z) (ho : Odd m) (h3 : 3 ≤ m) (hu : IsUnit (m : k)) (hp : PolFib t.G t.PP.L g M.pt)
    (hg : IsGenSec t.G t.PP.L _ θ) (hl : ThList t.G t.PP.L t.PP.rig m M.pt θ pt c) (hc : PCrd (M.pt ≫ h) c)
    (a : Fin (n + 1)) : ∃ s : LocSec t.G t.PP.L (h ⁻¹ᵁ chart k n a), IsLocSec s ∧
      ((((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)) ∧
      FibNz s (h ⁻¹ᵁ chart k n a)) := by
  by_cases hne : ((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty
  · have hloc := GlobalTheory.T.exists_localSection_thetaQuotient_projChart E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc a
    choose N hzN hNle s hs hgs hfs using hloc
    let κ := {z : M.Z // z ∈ h ⁻¹ᵁ chart k n a}
    have hsup : (⨆ z : κ, N z.1 z.2) = h ⁻¹ᵁ chart k n a :=
      le_antisymm (iSup_le fun z => hNle z.1 z.2) fun z hz =>
        TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzN z hz⟩
    obtain ⟨s', hs', hres⟩ := GlobalTheory.T.exists_glued_lineBundleSection_over_cover M.Z t.G t.PP.L (h ⁻¹ᵁ chart k n a) κ (fun z => N z.1 z.2) (fun z => s z.1 z.2)
      (fun z => hNle z.1 z.2) hsup (fun z => hs z.1 z.2) (fun z z' i =>
        GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen _ _ _ _ _ (hgs z.1 z.2) (hgs z'.1 z'.2) i)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.glued_section_generic_value_nonvanishing M.Z t.G t.PP.L Ω M.pt _ κ (fun z => N z.1 z.2) (fun z => s z.1 z.2) s' _
      (fun z => hNle z.1 z.2) hsup hres (fun z => hgs z.1 z.2) (fun z => hfs z.1 z.2)
    exact ⟨s', hs', fun _ => h1 ⟨⟨hne.some, hne.some_mem⟩⟩, h2⟩
  · refine ⟨0, isLocSec_zero, fun h' => absurd h' hne, fun K _ _ x hx => absurd ?_ hne⟩
    exact ⟨_, hx ⟨IsLocalRing.closedPoint K, rfl⟩⟩

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem app_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U) (x : Γ(X, U)) :
    (f.app V).hom (resG X e x) = resG Y (fun _ hy => e hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ((f.app U).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) : valF y V (resG X e f) = valF y U f := by
  unfold valF
  rw [dif_pos hV, dif_pos (hV.trans fun x hx => show y x ∈ U from e (show y x ∈ V from hx))]
  congr 1
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl

theorem val_res' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := rfl

theorem val_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl
end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

set_option maxHeartbeats 2000000 in

theorem pull_theta_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h hn ho h3 hu hp hth hc
  obtain ⟨θ, pt, hg, hl⟩ := hth
  choose s hs hgs hfs using chart_sec E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc
  have hcross := GlobalTheory.T.localThetaSections_ratio_coordinates_overlap k Ω M t.G t.PP.L n c h (SecM.ofSec t.G θ) hc (GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen)
  have hle : ∀ p : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).ι,
      (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U p ≤
        t.PP.L.U p.1 ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (p.2 PUnit.unit PUnit.unit)) := fun p y hy =>
    ⟨hy.1, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩
  refine ⟨⟨fun p => resG _ (hle p) (s _ p.1), fun p q => ?_⟩, fun K _ _ x => ?_⟩
  · obtain ⟨i, pj⟩ := p
    obtain ⟨i', qj⟩ := q
    have eB : ∀ (Y : Scheme.{0}) (φ : Y ⟶ M.Z) (u v : PUnit → PUnit → Fin (n + 1)),
        ((((ProjSpace.O1 k n).pull h).pull φ).g u v : Γ(Y, _)) =
          resG Y (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
              Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩ :
            (((ProjSpace.O1 k n).pull h).pull φ).U u ⊓ (((ProjSpace.O1 k n).pull h).pull φ).U v ≤
              φ ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (u PUnit.unit PUnit.unit) ⊓ chart k n (v PUnit.unit PUnit.unit))))
            ((φ.app _).hom ((h.app _).hom (ratioOn (chart k n (u PUnit.unit PUnit.unit) ⊓
              chart k n (v PUnit.unit PUnit.unit)) _ inf_le_left (v PUnit.unit PUnit.unit)))) := by
      intro Y φ u v
      have e1 := ProjSpace.linComb_punit_g ((ProjSpace.O1 k n).pull h) φ 1 u v
      have e2 := ProjSpace.linComb_punit_g (ProjSpace.O1 k n) h 1 (u PUnit.unit) (v PUnit.unit)
      rw [zpow_one] at e1 e2
      erw [e1]
      erw [e2]
      erw [val_res', val_pullU', val_res', val_pullU']
      rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit]
      erw [app_resG, resG_resG']
      rfl
    have hW1 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (pj PUnit.unit PUnit.unit) ⊓ chart k n (qj PUnit.unit PUnit.unit))) :=
      fun y hy => ⟨hy.1.1, (hle _ hy.1).2, (hle _ hy.2).2⟩
    have hW2 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.PP.L.U i' ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (qj PUnit.unit PUnit.unit)) :=
      fun y hy => ⟨⟨hy.1.1, hy.2.1⟩, (hle _ hy.2).2⟩
    have e1 := congrArg (resG t.G.left hW1) (hcross _ _ (s _) (s _) (hgs _) (hgs _) i)
    have e2 := congrArg (resG t.G.left hW2) (hs (qj PUnit.unit PUnit.unit) i i')
    rw [map_mul] at e1 e2
    erw [resG_resG', resG_resG', resG_resG'] at e1
    erw [resG_resG', resG_resG', resG_resG'] at e2
    show resG _ _ (resG _ (hle (i, pj)) (s (pj PUnit.unit PUnit.unit) i)) = _ *
      resG _ _ (resG _ (hle (i', qj)) (s (qj PUnit.unit PUnit.unit) i'))
    rw [resG_resG', resG_resG']
    erw [Units.val_mul, val_res', val_res', eB, resG_resG']
    rw [e1, e2, mul_left_comm, ← _root_.mul_assoc]
    rfl
  · obtain ⟨a, ha⟩ := exists_mem_chart k n (h (x (IsLocalRing.closedPoint K)))
    have hx : Set.range x ⊆ h ⁻¹ᵁ chart k n a := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
      exact ha
    obtain ⟨y, i, hyx, hyr, hv⟩ := hfs a K x hx
    have hyr' : Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U
        (i, fun _ _ => a) := fun _ hw =>
      ⟨(hyr hw).1, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => (hyr hw).2⟩
    refine ⟨y, (i, fun _ _ => a), hyx, hyr', ?_⟩
    show valF y _ (resG _ (hle (i, fun _ _ => a)) (s a i)) ≠ 0
    rwa [valF_resG y _ ((GlobalTheory.ZH.top_le_preimage_iff y _).2 hyr')]

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsPullbackAbelianScheme
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem finite_etale_ker {S : Scheme.{0}} (A : Over S) [GrpObj A] (k : ℕ)
    (hf : IsFinite (𝟙 A ^ k).left) (he : Etale (𝟙 A ^ k).left) :
    IsFinite (Ker A k).hom ∧ Etale (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).map (Over.forget S)
  have h₁ : IsFinite (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := hf
  have h₁' : Etale (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := he
  have h₂ : IsFinite (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h h₁
  have h₂' : Etale (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @Etale) h h₁'
  rw [← Over.w (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A])]
  exact ⟨MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S))),
    by haveI := h₂'; haveI : Etale (𝟙_ (Over S)).hom := inferInstanceAs (Etale (𝟙 S)); infer_instance⟩

end GlobalTheory.KerConst

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem isPullback_const_ker (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (G : Over (Spec (CommRingCat.of Ω))) [GrpObj G] : IsAbelianScheme G → ∀ (n : ℕ), (n : Ω) ≠ 0 →
    IsPullback (Sigma.desc (f := fun _ : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} =>
      𝟙_ (Over (Spec (CommRingCat.of Ω)))) fun x => x.1) (toUnit _) (𝟙 G ^ n) η[G] := by
  intro hG n hn
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have hu : IsUnit (n : Γ(Spec (CommRingCat.of Ω), ⊤)) := by
    have h1 : IsUnit (n : Ω) := hn.isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  obtain ⟨hfin, het⟩ := finite_etale_ker G n (GlobalTheory.GrpTangent.isFinite_id_pow G hu)
    (GlobalTheory.GrpTangent.etale_id_pow G hu)
  refine (isKer_iff (A := G) (k := n) (fun x : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} => x.1)
    (fun x => x.2)).2 ?_
  haveI := formallyUnramified_ker G hu
  haveI := locallyOfFiniteType_ker G n
  apply isIso_desc_of_lists
  intro K _ _ s u
  letI : Algebra Ω K := (Spec.preimage s).hom.toAlgebra
  have hs : s = spMap (algebraMap Ω K) := (Spec.map_preimage s).symm
  have hts : ∀ (T : Over (Spec (CommRingCat.of Ω))), (toUnit T).left = T.hom := fun T => by
    simpa using Over.w (toUnit T)
  obtain ⟨x₀, hx₀, hx⟩ := GlobalTheory.FinEtPoints.exists_point_of_finite_etale Ω K (Ker G n).left
    (Ker G n).hom hfin het u.left (by rw [Over.w u]; exact hs)
  let t₀ : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ Ker G n := Over.homMk x₀ hx₀
  have hp : (t₀ ≫ pullback.fst _ _) ^ n = 1 := by
    rw [← comp_mulBy, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  refine existsUnique_of_exists_of_unique ⟨⟨_, hp⟩, ?_⟩ ?_
  · have e : kerPt (t₀ ≫ pullback.fst _ _) hp = t₀ := ker_ext (kerPt_fst _ _)
    show toUnit _ ≫ kerPt (t₀ ≫ pullback.fst _ _) hp = u
    rw [e]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hts]
    show s ≫ x₀ = u.left
    exact (congrArg (· ≫ x₀) hs).trans hx
  · intro i j hi hj
    have h1 := congrArg (fun v => v ≫ pullback.fst _ _) (hi.trans hj.symm)
    simp only [Category.assoc, kerPt_fst] at h1
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left, hts] at h2
    haveI : Epi s := hs ▸ GlobalTheory.FinEtPoints.epi_spMap_field Ω K (algebraMap Ω K)
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi s).mp h2))

end GlobalTheory.KerConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistLowerBoundAlt
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem twGe : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → TwAdm → TwChr → TwGe := by
  intro h1 h2 h3 h4 hA hC
  have h4' := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS h4
  have hD := GlobalTheory.T.realization_embedding_compatible
  have hR := GlobalTheory.T.exists_coefficient_lattice_span h1 h2 h3 h4'
  have hG := GlobalTheory.T.twisted_embedding_compatibility_rows h1 h2 h3 h4' hA hC
  have hS := GlobalTheory.T.twisted_ring_embedding_rows
  unfold TwGe
  unfold AtFit AtTw AtPts at hD hG hS ⊢
  unfold AtTw AtPts at hR
  refine (((hD.and hR).and hG).and hS).imp fun Fm CH _ H => ?_
  obtain ⟨x0, hx0⟩ := ((H.1.1.1.and H.1.1.2).and H.1.2).and H.2
  refine ⟨x0, fun x hx h0 i p hp hM w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hx0 x hx h0 i p hp
  have d := k1 hM w hw j ρ hρ ν rd hfit hcan
  have r := k2 hM w hw j
  have g := k3 hM w hw j ρ hρ ν rd hfit hcan
  have s := k4 hM w hw j ρ hρ ν rd hfit hcan
  obtain ⟨-, e, he1, he2⟩ := hfit.1
  unfold twLat
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, h, w', a, κ, N, hN, hκ, hhw, ha⟩ := g e he1 he2 z hz
  choose y hy hyv using fun k => r (h k) (hhw k).1 (w' k) (hhw k).2
  obtain ⟨b, hb⟩ := s e he1 he2 z n a y κ N hy hN hκ (ha y hyv)
  rw [d e he1 he2 z n (fun k => b * a k) y hy hb]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y k,
    Submodule.subset_span ⟨h k, (hhw k).1, w' k, (hhw k).2, fun v => ?_⟩, rfl⟩)
  rw [one_smul]
  exact hyv k v

end GlobalTheory.BigOn.Exp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuationStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_colength_range_eq_det_valuation : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  first | exact @GlobalTheory.Dieu.ColenDet.colength_det | exact GlobalTheory.Dieu.ColenDet.colength_det | (intros; apply GlobalTheory.Dieu.ColenDet.colength_det <;> assumption)
end

