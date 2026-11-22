import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelGoodReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.USpreadU

open GlobalTheory.Poinc.GalTrans GlobalTheory.CechPic

theorem exists_model {O Ω R' R'' : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R'']
    (f' : R' →+* O) (f'' : R'' →+* O) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (B : PolAV (Sp O)) (c' : B.A.left ⟶ P'.A.left) (c'' : B.A.left ⟶ P''.A.left) (j : Q.A.left ⟶ B.A.left),
      IsGrpPullback B.A P'.A (spMap f') c' ∧ IsGrpPullback B.A P''.A (spMap f'') c'' ∧
      LBIso B.L (P'.L.pull c') ∧ LBIso B.L (P''.L.pull c'') ∧
      IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j ∧ j ≫ c' = b' ∧ j ≫ c'' = b'' ∧
      ∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp O ⟶ B.A.left, w₀ ≫ B.A.hom = 𝟙 _ ∧ w₀ ≫ c' = spMap f' ≫ t' ∧ w₀ ≫ c'' = spMap f'' ≫ t'' := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  refine ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej, ej'', fun t' t'' w ht' ht'' hw e' e'' => ?_⟩
  have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
  have k₁ := hc'.1.lift_fst _ _ w₁
  have k₂ := hc'.1.lift_snd _ _ w₁
  generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
  have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
    (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
    (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
  have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
    (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
    (spMap (algebraMap O Ω))
    (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
  exact ⟨t, k₂, k₁, a₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  intro E _ _ _ H Dw l Xo cf C X σ s hs p _ y S' S'' ρ' ρ'' h' h'' y₀ y₁ hy₀ hy₁ u u₁ u' u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ k₀'' hk₀ hk₀'' hkb
  haveI := X.ar.char
  set z := y (closedPoint (PadicAlgCl p)) with hz
  have hyz : Set.range y = {z} := RatModel.range_eq_singleton y _
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z) := X.M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z) := X.normal.isIntegrallyClosed_stalk z
  haveI : IsIntegrallyClosed (X.M.O z) := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z)

  have hU : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X.M.O z) := fun n hn => by
    rw [← RatModel.val_ne_zero_iff hyz]
    have e := map_intCast (RatModel.valHom y z hyz) n
    rw [RatModel.valHom_apply] at e
    rw [e]
    exact Int.cast_ne_zero.2 hn
  have hmem : ∀ {x : X.Ω₁} (n : ℤ), n ≠ 0 → (n : X.Ω₁) * x ∈ X.M.O z → x ∈ X.M.O z := fun {x} n hn h => by
    obtain ⟨w, hw⟩ := hU n hn
    have e1 : (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * (n : X.Ω₁) = 1 := by
      have := congrArg (fun t : X.M.O z => (t : X.Ω₁)) w.inv_mul
      simpa [hw] using this
    have : x = (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * ((n : X.Ω₁) * x) := by rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem (SetLike.coe_mem _) h
  have hR' : ratHull S'.R ≤ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    exact hmem n hn (h' h)
  have hR'' : ∀ x ∈ ratHull S''.R, σ x ∈ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine hmem n hn ?_
    have := map_mem_O hs (h'' h)
    rwa [map_mul, map_intCast] at this
  let f'Q : ratHull S'.R →+* X.M.O z := (Subalgebra.inclusion hR').toRingHom
  let f''Q : ratHull S''.R →+* X.M.O z := (σ.comp (ratHull S''.R).val.toRingHom).codRestrict (X.M.O z) fun x => hR'' x x.2
  let f' : S'.R →+* X.M.O z := f'Q.comp (toRat S'.R)
  let f'' : S''.R →+* X.M.O z := f''Q.comp (toRat S''.R)

  obtain ⟨Q, c, hc, lc⟩ := exists_pol_baseChange ρ'.P (spMap S'.R.val.toRingHom)
  have hW : IsGrpPullback W₀ ρ'.P.A (spMap S'.R.val.toRingHom) (k₀ ≫ α) :=
    (hk₀.comp hα).congr (spMap_val_toRat S'.R) rfl
  have ec : hW.1.lift c Q.A.hom hc.1.w ≫ k₀ ≫ α = c := hW.1.lift_fst _ _ _
  have ew : hW.1.lift c Q.A.hom hc.1.w ≫ W₀.hom = Q.A.hom := hW.1.lift_snd _ _ _
  generalize hW.1.lift c Q.A.hom hc.1.w = e at ec ew
  have he : IsGrpPullback Q.A W₀ (𝟙 _) e :=
    hW.cancel (hc.congr (Category.id_comp _).symm ec.symm) (by rw [ew, Category.comp_id])
  have hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) (e ≫ k₀'' ≫ α'') :=
    (he.comp (hk₀''.comp hα'')).congr (by rw [Category.id_comp]; exact sp_comp (RingHom.ext fun _ => rfl)) rfl
  have hA : pull α (cls ρ'.P.L ρ'.P.isLB) = pull β (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ'.P.isLB α (pull_isLB ρ'.P.isLB α)]
    exact (iso_iff (pull_isLB ρ'.P.isLB α) Xo.univ.t.PP.isLB β).1 hL
  have hA'' : pull α'' (cls ρ''.P.L ρ''.P.isLB) = pull β'' (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ''.P.isLB α'' (pull_isLB ρ''.P.isLB α'')]
    exact (iso_iff (pull_isLB ρ''.P.isLB α'') Xo.univ.t.PP.isLB β'').1 hL''
  have hk : pull k₀ (pull β (cls _ Xo.univ.t.PP.isLB)) = pull k₀'' (pull β'' (cls _ Xo.univ.t.PP.isLB)) := by
    rw [← pull_comp, ← pull_comp, hkb]
  have lb'' : LBIso Q.L (ρ''.P.L.pull (e ≫ k₀'' ≫ α'')) := by
    rw [iso_iff Q.isLB ρ''.P.isLB, (iso_iff Q.isLB ρ'.P.isLB _).1 lc, ← ec]
    simp only [pull_comp]
    rw [hA, hA'', hk]

  obtain ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej', ej'', ht⟩ :=
    exists_model f' f'' ρ'.P ρ''.P Q (b' := c) (b'' := e ≫ k₀'' ≫ α'') hc hb'' lc lb''

  let v : X.M.O z →+* PadicAlgCl p := RatModel.valHom y z hyz
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d, hd, ld⟩ := exists_pol_baseChange B (spMap v)
  have hd' : IsGrpPullback P₀.A ρ'.P.A (spMap y₀) (d ≫ c') := (hd.comp hc').congr (sp_comp e₀) rfl
  have hd'' : IsGrpPullback P₀.A ρ''.P.A (spMap y₁) (d ≫ c'') := (hd.comp hc'').congr (sp_comp e₁) rfl
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' (lb_comp P₀.isLB B.isLB ρ'.P.isLB ld lc')
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u₁ P₀ hd'' (lb_comp P₀.isLB B.isLB ρ''.P.isLB ld lc'')
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c1 c2 => ?_, fun v₁ g h hv₁ hg hh => ?_⟩
  · have ww : w ≫ W₀.hom = 𝟙 _ ≫ 𝟙 _ := by rw [hw]; simp
    have q1 : he.1.lift w (𝟙 _) ww ≫ e = w := he.1.lift_fst _ _ _
    have q2 : he.1.lift w (𝟙 _) ww ≫ Q.A.hom = 𝟙 _ := he.1.lift_snd _ _ _
    generalize he.1.lift w (𝟙 _) ww = wQ at q1 q2
    obtain ⟨w₀, hw₀, g', g''⟩ := ht (ρ'.pt k').left (ρ''.pt k'').left wQ (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k''))
      q2 (by rw [← ec, reassoc_of% q1, c1]; rfl) (by rw [reassoc_of% q1, c2]; rfl)
    have w₂ : (spMap v ≫ w₀) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, hw₀]; simp
    have r1 : hd.1.lift _ _ w₂ ≫ d = spMap v ≫ w₀ := hd.1.lift_fst _ _ _
    have r2 : hd.1.lift _ _ w₂ ≫ P₀.A.hom = 𝟙 _ := hd.1.lift_snd _ _ _
    generalize hd.1.lift _ _ w₂ = wK at r1 r2
    obtain ⟨x, hx⟩ := xa wK r2
    obtain ⟨x', hx'⟩ := xa' wK r2
    refine ⟨wK, x, x', r2, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, reassoc_of% r1, g', ← Category.assoc, sp_comp e₀]
    · rw [← hx', Category.assoc, ea', reassoc_of% r1, g'', ← Category.assoc, sp_comp e₁]

  ·
    have wm' : c' ≫ ρ'.P.A.hom = (B.A.hom ≫ spMap f'Q) ≫ spMap (toRat S'.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc'.1.w
    have wm'' : c'' ≫ ρ''.P.A.hom = (B.A.hom ≫ spMap f''Q) ≫ spMap (toRat S''.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc''.1.w
    have m1 : hα.1.lift c' _ wm' ≫ α = c' := hα.1.lift_fst _ _ _
    have m2 : hα.1.lift c' _ wm' ≫ G.hom = B.A.hom ≫ spMap f'Q := hα.1.lift_snd _ _ _
    have m1'' : hα''.1.lift c'' _ wm'' ≫ α'' = c'' := hα''.1.lift_fst _ _ _
    have m2'' : hα''.1.lift c'' _ wm'' ≫ G''.hom = B.A.hom ≫ spMap f''Q := hα''.1.lift_snd _ _ _
    generalize hα.1.lift c' _ wm' = m' at m1 m2
    generalize hα''.1.lift c'' _ wm'' = m'' at m1'' m2''
    have key : m' ≫ β = m'' ≫ β'' := by
      haveI := Xo.univ.proper
      haveI : IsSeparated Xo.s := GlobalTheory.LevelQuotRep.isSeparated_of_qproj Xo.qproj
      obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap (X.M.O z) X.Ω₁)) ∧
          IsSchemeTheoreticallyDominant (spMap (algebraMap (X.M.O z) X.Ω₁)) :=
        ExtUnique.spec_fractionRing (X.M.O z) X.Ω₁
      haveI := B.isAb.smooth
      haveI : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
      refine ExtUnique.hom_ext_of_dominant (Xo.univ.t.G.hom ≫ Xo.s ≫ terminal.from _) (terminal.hom_ext _ _) j ?_
      have n1a : (j ≫ m') ≫ α = (e ≫ k₀) ≫ α := by rw [Category.assoc, m1, ej', Category.assoc, ec]
      have n1b : (j ≫ m') ≫ G.hom = (e ≫ k₀) ≫ G.hom := by
        rw [Category.assoc, m2, reassoc_of% hj.1.w, Category.assoc, hk₀.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n1 : j ≫ m' = e ≫ k₀ := hα.1.hom_ext n1a n1b
      have n2a : (j ≫ m'') ≫ α'' = (e ≫ k₀'') ≫ α'' := by rw [Category.assoc, m1'', ej'', Category.assoc]
      have n2b : (j ≫ m'') ≫ G''.hom = (e ≫ k₀'') ≫ G''.hom := by
        rw [Category.assoc, m2'', reassoc_of% hj.1.w, Category.assoc, hk₀''.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n2 : j ≫ m'' = e ≫ k₀'' := hα''.1.hom_ext n2a n2b
      rw [reassoc_of% n1, reassoc_of% n2, hkb]
    have hg' : g ≫ α = v₁ ≫ d ≫ c' := by rw [hg, ea]
    have hh' : h ≫ α'' = v₁ ≫ d ≫ c'' := by rw [hh, ea']
    have g1 : g = v₁ ≫ d ≫ m' := hα.1.hom_ext (by rw [hg', Category.assoc, Category.assoc, m1])
      ((existsUnique_ratPoint S'.R (g ≫ α ≫ ρ'.P.A.hom)).unique (by rw [Category.assoc, hα.1.w])
        (by simp only [Category.assoc]; rw [← hα.1.w, reassoc_of% m1, ← reassoc_of% hg']))
    have h1 : h = v₁ ≫ d ≫ m'' := hα''.1.hom_ext (by rw [hh', Category.assoc, Category.assoc, m1''])
      ((existsUnique_ratPoint S''.R (h ≫ α'' ≫ ρ''.P.A.hom)).unique (by rw [Category.assoc, hα''.1.w])
        (by simp only [Category.assoc]; rw [← hα''.1.w, reassoc_of% m1'', ← reassoc_of% hh']))
    rw [g1, h1]; simp only [Category.assoc, key]

end GlobalTheory.UPoinc.USpreadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinearStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valR_imageModelSection_semilinear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (τ : 𝓞 K →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p τ), y ∈ GlobalTheory.CxPts.ptsIn p τ (L.B.U i) → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) = ∑ k, τ (β k) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s (u k)).f i) := by
  first | exact @GlobalTheory.ImageModel.valR_section_sum | exact GlobalTheory.ImageModel.valR_section_sum | (intros; apply GlobalTheory.ImageModel.valR_section_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLowerBoundProductStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lower_bound_product : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ),
    (l : R) ∈ IsLocalRing.maximalIdeal R → (l : R) ≠ 0 →
    ∀ (a b δ : FractionRing R) (u : Rˣ) (ca cd : ℚ), a ≠ 0 → b ≠ 0 → δ ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l a ≤ (ca : WithTop ℚ) → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l b ≤ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l δ = (cd : WithTop ℚ) →
      ((-(ca + cd) : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) (u : R)) ^ 2 / (a * (δ * b))) := by
  first | exact @GlobalTheory.ValArith.val_sq_div_ge | exact GlobalTheory.ValArith.val_sq_div_ge | (intros; apply GlobalTheory.ValArith.val_sq_div_ge <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationPlacesCompatibleTower
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LocalDegreeOne

open scoped Pointwise

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (L L' : IntermediateField E Ω) (hL : FiniteDimensional E L) (hL' : FiniteDimensional E L'), L ≤ L' →
    haveI := hL; haveI := hL'; haveI : NumberField L := NumberField.of_module_finite E L
    haveI : NumberField L' := NumberField.of_module_finite E L'
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)) (v' : HeightOneSpectrum (𝓞 L')),
      IsPlaceOver A v → IsPlaceOver A v' →
      (∀ σ : Ω ≃ₐ[E] Ω, σ ∈ A.decompositionSubgroup E → (∀ x ∈ L, σ x = x) → ∀ x ∈ L', σ x = x) →
      v'.asIdeal.ramificationIdx (𝓞 E) = v.asIdeal.ramificationIdx (𝓞 E) ∧ normV v' = normV v := by
  intro E Ω _ _ _ _ _ L L' hL hL' hLL'
  haveI := hL
  haveI := hL'
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : NumberField L' := NumberField.of_module_finite E L'
  intro A v v' hv hv' hfix
  letI : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra
  haveI : IsScalarTower L L' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower E L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI : IsAlgClosure L' Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L'⟩
  haveI : Module.Finite L L' := Module.Finite.of_restrictScalars_finite E L L'
  haveI : NumberField (IntermediateField.normalClosure L L' Ω) :=
    NumberField.of_module_finite L (IntermediateField.normalClosure L L' Ω)
  haveI : IsAlgClosure (IntermediateField.normalClosure L L' Ω) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := L) (IntermediateField.normalClosure L L' Ω)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (K := L) (L := IntermediateField.normalClosure L L' Ω) hv
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := L') hv hv' hP (by
    intro σ hσ
    have h1 : σ.restrictScalars E ∈ A.decompositionSubgroup E := hσ
    have h2 : ∀ x ∈ L, σ.restrictScalars E x = x := fun x hx => σ.commutes ⟨x, hx⟩
    have h3 := hfix _ h1 h2
    exact ⟨{ σ.toRingEquiv with commutes' := fun y => h3 _ y.2 }, AlgEquiv.ext fun _ => rfl⟩)
  haveI : v'.asIdeal.LiesOver v.asIdeal := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hv hv'
  constructor
  · rw [Ideal.ramificationIdx_tower (R := 𝓞 E) v.asIdeal v'.asIdeal, he, mul_one]
  · have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal
    rw [hf, pow_one] at h
    simp only [normV]
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Ideal.absNorm_apply, h]

end GlobalTheory.LocalDegreeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSqrtNegPrimeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  first | exact @GlobalTheory.val_vp_sqrt_neg_prime | exact GlobalTheory.val_vp_sqrt_neg_prime | (intros; apply GlobalTheory.val_vp_sqrt_neg_prime <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueUnitSectionSmulGenericFibreSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_unitSection_smul_genericFibre_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.UnitGen.value_unit_generic | exact GlobalTheory.Mum.UnitGen.value_unit_generic | (intros; apply GlobalTheory.Mum.UnitGen.value_unit_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuedConvolution_cancel_injective_latticeHom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  first | exact @GlobalTheory.UT.sumV_cancel_hom | exact GlobalTheory.UT.sumV_cancel_hom | (intros; apply GlobalTheory.UT.sumV_cancel_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmpleAlongPullback_transport_iso : ∀ {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn], gn ≫ pA = p → ∀ (π : Y ⟶ X) {L : LB X}, L.IsLB → ∀ {LA : LB XA}, LA.IsLB → ∀ {k m : ℕ} (b : Fin (m + 1) → H0 LA k), VeryAmpleAlong pA (𝟙 XA) LA b → ∀ (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ), (∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) → ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j = u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) → VeryAmpleAlong p π L σ := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_transport | exact GlobalTheory.Mum.veryAmpleAlong_transport | (intros; apply GlobalTheory.Mum.veryAmpleAlong_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_complexPoints_properClosed_chart_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  first | exact @GlobalTheory.ChernNull.chart_null_field | exact GlobalTheory.ChernNull.chart_null_field | (intros; apply GlobalTheory.ChernNull.chart_null_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelGoodReductionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_model_good_reduction : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (J : ℂ), IsIntegral ℤ J →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧ ((W.c₄ : R₁) : ℂ) ^ 3 = J * ((W.Δ : R₁) : ℂ) := by
  first | exact @GlobalTheory.PlaceRingCurve.exists_curve | exact GlobalTheory.PlaceRingCurve.exists_curve | (intros; apply GlobalTheory.PlaceRingCurve.exists_curve <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVectorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (m k : ℕ), S.N = m ^ 2 → 2 ≤ k → k ∣ m → ∀ ν : u.D.toPre.X, (∀ χ : u.D.toPre.X, m • χ ≠ 0 → l.q ν < l.q (ν + m • χ)) → ∃ h ∈ l.yy.ker, k • m • h = 0 ∧ ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀ * Real.exp (-l.q ν) := by
  first | exact @GlobalTheory.UPoinc.ExactWeight.main | exact GlobalTheory.UPoinc.ExactWeight.main | (intros; apply GlobalTheory.UPoinc.ExactWeight.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.LineForm

theorem chain_sum_coordVec {n : ℕ} (w : V n) : w = ∑ b, w b • coordVec b := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem del_dbar_comp_holo_pull : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m),
    DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  intro m n τ c v hτ hc
  constructor
  · simp only [del_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
    simp only [map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]
  · simp only [dbar_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
    simp only [map_sum, map_smulₛₗ, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

end GlobalTheory.LineForm
end

