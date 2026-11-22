import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesStabilizerInvariant
section
namespace GlobalTheory.AdForm.StabTrans
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

theorem chi_stab {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : Ch → GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U)
    (hy : (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1) :
    ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
  have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
  have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
  have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
  have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
  have h4 : ratAd B.host.F (s.1.1⁻¹) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
      ((I.stp u a i).gam c.1 s.1))⁻¹ := by
    rw [ratAd, map_inv, map_inv]
    rfl
  rw [h4, h3 _ _ _ _ hy, ← h2] at h1
  exact hR.chr c κ (1, s.1.2) (map_one (_root_.Formalism.L2.Col.ufGL B.fields.E (B.R.N i))) h1

end GlobalTheory.AdForm.StabTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabTrans
open Formalism.L2.Theta

theorem finM_mul' {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem rTrans_mul {G : Type} [Monoid G] (a b : G) (F : G → ℂ) : rTrans (a * b) F = rTrans a (rTrans b F) := by
  funext x
  simp only [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans (1 : G) F = F := by
  funext x
  simp only [rTrans, mul_one]

theorem rTrans_list_prod {G α : Type} [Monoid G] (f : α → G) (F : G → ℂ) (h : ∀ i, rTrans (f i) F = F) :
    ∀ L : List α, rTrans (L.map f).prod F = F
  | [] => by simpa using rTrans_one F
  | i :: L => by
    rw [List.map_cons, List.prod_cons, rTrans_mul, rTrans_list_prod f F h L, h i]

end GlobalTheory.AdForm.StabTrans

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.AdForm.trans_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv e s
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hR := hA.reads j hj
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY ⟨A.kb j, hR⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf j e))
  have hAd : Ψ ∈ AdFun (A.K j hj (A.chOf j e)).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
  have hfun : (fun (c : {c // A.chOf j c = A.chOf j e}) (z : Frames (gramC (gramN (I.rec7 l Z) j hj) (embT (I.rec7 l Z)))) =>
      φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K j hj (A.chOf j e)).y c) := he.symm
  have rdΨ : ∀ (w : (I.chain l u a).Y j) (g0 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), g0 ∈ GfC _ →
      ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
      x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) g0 →
      A.rd θ j hj (A.chOf j e) φ w g0 = Ψ x ⟨w.1, w.2⟩ := by
    intro w g0 hg0 x hx
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj (A.chOf j e)).lev _
      (A.K j hj (A.chOf j e)).y (A.K j hj (A.chOf j e)).y_bij Ψ hAd ⟨w.1, w.2⟩ g0).2.2 x ⟨w.1, w.2⟩ hx (fun τ => by
        have h1 := GlobalTheory.AdForm.ChartVal.infM_fin' θ _ (rankN (I.rec7 l Z) j hj) g0 hg0 τ
        show w.1 τ = infM θ _ _ g0 τ * w.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) j hj) (A.K j hj (A.chOf j e)).lev (A.K j hj (A.chOf j e)).y
      (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨w.1, w.2⟩ g0 = _
    rw [hfun]
    exact hval
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = Formalism.L2.Col.embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  refine ((GlobalTheory.Mem.Col2.ValTie.stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) j hj) (I.stp u a j) B.fields.emb B.embLL e (A.K j hj (A.chOf j e)).lev hemb
    ((A.K j hj (A.chOf j e)).y ⟨e, rfl⟩).1 ((A.K j hj (A.chOf j e)).stabI ⟨e, rfl⟩) (hR.stab e)
    ((A.K j hj (A.chOf j e)).stabI_range ⟨e, rfl⟩)
    (GlobalTheory.AdForm.StabTrans.chi_stab I hI l Z u a j hj (A.chOf j) (A.K j hj) (A.kb j) hR e)
    _ (fun z => ⟨z.1, z.2⟩) (fun _ => rfl)).2 ?_) s
  intro γ hγ κ hy z z' hz

  clear hF hV he hΨ
  obtain ⟨⟨eι, -⟩, -⟩ := id hT
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  classical
  have hJnd : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList _
  have hJall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨hlev1, hlev2⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hI hP l Z u a Ch A hA k ι p β Q L hT _ hJnd hJall j hj (A.chOf j e)
  obtain ⟨kA, hkAf, hkAe⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)
    ⟨κ.1, (((A.K j hj (A.chOf j e)).lev.U_eq κ.1).1 κ.2).1⟩
  have hkAU : kA ∈ A.U j (A.chOf j e) := (hA.U j hj _ kA).2 ⟨hkAf, κ, hkAe.symm⟩
  obtain ⟨g, hg, κ', hκ'off, hdec⟩ := hlev2 kA hkAU
  have hPK : ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod ∈
      (A.chi j (A.chOf j e)).ker.map (A.U j (A.chOf j e)).subtype := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h, h1⟩ := hlev1 i (g i) (hg i)
    exact ⟨⟨_, h⟩, h1, rfl⟩
  obtain ⟨P0, hP0chi, hP0e⟩ := Subgroup.mem_map.1 hPK
  rw [MonoidHom.mem_ker] at hP0chi
  set P := ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod with hPdef
  have hP0e' : P0.1 = P := hP0e
  have hκ'U : κ' ∈ A.U j (A.chOf j e) := by
    have : κ' = P0.1⁻¹ * kA := by rw [hdec, hP0e']; group
    rw [this]
    exact mul_mem (inv_mem P0.2) hkAU
  obtain ⟨κ'', hκ''⟩ := ((hA.U j hj _ κ').1 hκ'U).2
  have hchi : ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) = ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) := by
    rw [← hA.chi j hj _ ⟨kA, hkAU⟩ κ hkAe.symm, ← hA.chi j hj _ ⟨κ', hκ'U⟩ κ'' hκ'']
    have e1 : (⟨kA, hkAU⟩ : A.U j (A.chOf j e)) = P0 * ⟨κ', hκ'U⟩ := Subtype.ext (by
      show kA = P0.1 * κ'
      rw [hP0e', hdec])
    rw [e1, map_mul, hP0chi, one_mul]

  obtain ⟨-, -, hAtF, -, hcm, -, -, hOff, -⟩ := GlobalTheory.FinPl.SetCut.grp_split (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (Finset.univ.image fun i => (p i).v)
  have hPQ : (fun x => ∃ i, x = (p i).v) = (· ∈ (Finset.univ.image fun i => (p i).v)) := by
    funext x
    apply propext
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hκ'at : κ' ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ (Finset.univ.image fun i => (p i).v)) := by
    have h1 : κ' ∈ GfC _ ⊓ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v) :=
      ⟨((hA.U j hj _ κ').1 hκ'U).1, hκ'off⟩
    rw [hOff] at h1
    have hPQn : (fun x => ¬ ∃ i, x = (p i).v) = (· ∉ (Finset.univ.image fun i => (p i).v)) :=
      funext fun x => congrArg Not (congrFun hPQ x)
    rw [hPQn] at h1
    exact h1
  have hcomm : ∀ g' ∈ c.support, g' * κ' = κ' * g' := fun g' hg' => hcm g' (hPQ ▸ hc g' hg') κ' hκ'at
  have hsuppF : ∀ g' ∈ c.support, g' ∈ GfC ((I.rec7 l Z).sp.X j) := fun g' hg' => hAtF (hPQ ▸ hc g' hg')
  have hPf : P ∈ GfC ((I.rec7 l Z).sp.X j) := hP0e' ▸ ((hA.U j hj _ P0.1).1 P0.2).1
  have hhe := hA.h j hj (A.chOf j e) ⟨e, rfl⟩
  have term : ∀ g' ∈ c.support, A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * g') =
      ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) * A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g') := by
    intro g' hg'
    obtain ⟨x1, hx1⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * g')
    obtain ⟨x2, hx2⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g')
    have a1 := rdΨ ⟨z.1, z.2⟩ _ (mul_mem hhe.1 (hsuppF g' hg')) x1 hx1
    have a2 := rdΨ ⟨z'.1, z'.2⟩ _ (mul_mem (mul_mem hhe.1 hPf) (hsuppF g' hg')) x2 hx2
    rw [a1, a2]
    refine hAd γ hγ x2 x1 κ'' ?_ z z' hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx1, hx2, hκ'']
    have hyv := congrArg Units.val hy
    erw [Units.val_mul, Units.val_mul] at hyv
    have hk : kA * g' = P * g' * κ' := by rw [hdec, mul_assoc, ← hcomm g' hg', ← mul_assoc]
    have e2 := congrArg (finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)) hk
    simp only [StabTrans.finM_mul'] at e2 ⊢
    conv_lhs => rw [hhe.2, hyv, ← hhe.2]
    erw [← hkAe]
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← e2]
    try rfl
  have hinvP := congrFun (StabTrans.rTrans_list_prod (fun i => (β j i).gl (g i)) (trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩))
    (fun i => hinv _ _ i (g i) (hg i)) (Finset.univ : Finset ι).toList) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hPdef] at hinvP
  show trc c (A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩) =
    ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) * trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hinvP, hchi]
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  rw [term g' hg']
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest

theorem isTypePlaces_vGs {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (h : I.Ok) :
    GlobalTheory.Core.Mi.IsTypePlaces (D := I.rec7 l Z) (B.primes X).vGs := by
  classical
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit (I.rec7 l Z) (TC.cf I l Z)
  have hP : L.Pg = (B.primes X).vGs := by
    ext w
    rw [hL.Pg w, hC]
    have hv : w ∈ (B.primes X).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
      rw [← h.pibar 0 w, ← h.pibar 1 w]
      exact @Finset.mem_union _ (_) _ _ _
    exact (hv.trans (Fin.exists_fin_two (p := fun k => I.C.P.Div k w)).symm).symm
  rw [← hP]
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh hL

end GlobalTheory.Fam.ColTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KJRealLive

theorem castP_mvZ {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (M : D.what₂.Tau → Matrix (Fin p) (Fin p) ℂ)
    (M' : D.what₂.Tau → Matrix (Fin q) (Fin q) ℂ) (P : PolF D q p) :
    castP (D := D) hp hq (mvZ M M' P) =
      mvZ (fun τ => (M τ).reindex (finCongr hp) (finCongr hp)) (fun τ => (M' τ).reindex (finCongr hq) (finCongr hq))
        (castP (D := D) hp hq P) := by
  subst hp; subst hq
  rw [Sized.castP_rank, Sized.castP_rank]
  have h : ∀ n (N : Matrix (Fin n) (Fin n) ℂ), N.reindex (finCongr rfl) (finCongr rfl) = N := fun n N => by ext; simp
  simp only [h]

theorem comb_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (x : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (x • f) = x • comb ψ S T c f := by
  funext u
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KJRealLive

open GlobalTheory.KJRealLive in

theorem GlobalTheory.KJRealLive.clsKL_real : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  intro j hj α γ k₁ hk₁ k₂ hk₂ P₁ P₂ hP₁₂
  have hjle : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hjlt : j < B.R.m := hj
  obtain ⟨e, he, hee⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u a Ch₀ A hP.is j hj
  have hvac := hX.vc j hjlt
  have hxj := hX.xs j hjle
  have hxj1 := hX.xs (j + 1) hj
  have hW := hP.om j hjlt
  have hfin := (hP.dat j hj α γ).1
  have hstd := hX.std
  have hth0 : IsThetaFunO R.ψ _ _ (g.vac j) := hvac.2.theta
  have eS : Even ((I.rec7 l Z).sp.X j).rank := by rw [rankN (I.rec7 l Z) j hjle]; exact even_rankN _ j
  have eT : Even ((I.rec7 l Z).sp.X (j + 1)).rank := by rw [rankN (I.rec7 l Z) (j + 1) hj]; exact even_rankN _ (j + 1)
  have key := GlobalTheory.KJReal.om_pureTensorO_onb (I.rec7 l Z) R.ψ R.θ _ _ (g.x j) (g.x (j + 1)) (A.chr (j + 1)) (k.kom j) hX.inf
    (hx j hjle) (hx (j + 1) hj) hxj.1 hxj1.1 eS eT hW e he (g.vac j) hth0 hvac.2.fock k₁ hk₁ k₂ hk₂
  have hPP : P₂ = mvZ (fun τ => (inB R.θ _ (g.x j).B k₁ τ)⁻¹) (inB R.θ _ (g.x (j + 1)).B k₂) P₁ := by
    apply (Sized.castP_bijective (D := I.rec7 l Z) (rankN (I.rec7 l Z) j hjle) (rankN (I.rec7 l Z) (j + 1) hj)).1
    refine hP₁₂.trans ?_
    rw [castP_mvZ]
    congr 2
    funext τ
    exact Matrix.inv_reindex _ _ _
  have hs1 : ∀ τ, (realOf u R g s J).sS j τ = -e τ - (((I.rec7 l Z).sp.X (j + 1)).rank : ℤ) / 2 := fun τ => (hee τ).1
  have hs2 : ∀ τ, -(realOf u R g s J).sD j τ = e τ + (((I.rec7 l Z).sp.X j).rank : ℤ) / 2 := fun τ => (hee τ).2.1
  have hpt0 : IsThetaFunO R.ψ _ _ (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B (g.vac j) P₁) :=
    GlobalTheory.FockTheta.ptStable _ R.ψ R.θ hstd hX.inf _ _ _ _ _ _ _ P₁ hth0
  show k.kom j (k₁, k₂) (pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₁) = _ • pureTensorO R.ψ R.θ _ _ (g.x j).s (g.x (j + 1)).s (g.x j).B (g.x (j + 1)).B
    (comb R.ψ _ _ (k.dd j α γ) (g.vac j)) P₂
  rw [LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, GlobalTheory.FrComb.om_comb hW hk₁ hk₂ hfin hpt0, key, comb_smul,
    LiftsAtLevel.comb_pureTensorO hstd hX.inf _ _ _ _ hth0 hfin, hPP]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs1 τ, hs2 τ]
  show _ = ((inB R.θ _ (g.x j).B k₁ τ).reindex _ _).det ^ _ * ((inB R.θ _ (g.x (j + 1)).B k₂ τ).reindex _ _).det ^ _
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelComparison
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevPrime

section Comp

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_eq_one_of_off (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  subst hn
  have h := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  have e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j) := by rw [hx]; rfl
  rw [e, prV_toEAf_congr v h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end Comp

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}

theorem exists_splitPt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : ∃ i, v = (p i).v := by
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl
    (l.pr.piT_norm u) hne v).1 hv
  obtain ⟨e, he⟩ := hS.1
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  have h := he (e.symm ⟨w, hw⟩)
  rw [e.apply_symm_apply] at h
  exact (GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm

set_option maxHeartbeats 2000000 in

theorem uloc_le_of_std (hOk : I.Ok) (hP : TC.Pins B X) {a a' : I.ι} {Ch Ch' : ℕ → Type} {A : TwDat I l Z u a Ch}
    {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (J : List ι) (hn : J.Nodup) (hall : ∀ i, i ∈ J) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j) (b' : Ch' j)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ∃ i, v = (p i).v) :
    (A.K j hj b).lev.Uloc v ≤ (A'.K j hj b').lev.Uloc v := by
  intro h hh
  obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) x = h := by
    refine ⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, Formalism.UG.P.afsplit_right1 v h 1]; exact hh
    · have hxw : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
          Units.val_one, Units.val_one]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hxw]; exact one_mem _
  obtain ⟨g, hgC, hg⟩ := GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩
  have hgU : g ∈ A.U j b := (hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩
  obtain ⟨g', hg', κ', hκ', hκe⟩ := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU
  have hst := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1
  have hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b' := Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (hst i _ (hg' i)).1
  obtain ⟨-, y, hy⟩ := (hA'.U j hj b' _).1 hprod
  obtain ⟨z, hz⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'
  have e : x = y.1 * z.1 := by
    apply Units.ext
    have hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1 := hg
    rw [Units.val_mul, hy, hz, ← hg2, hκe]
    exact GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _
  have hz1 := bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz
  rw [← hxv, e, map_mul, hz1, mul_one]
  exact (((A'.K j hj b').lev.U_eq _).1 y.2).2 v

end Level

set_option maxHeartbeats 2000000 in

theorem uloc_le_levelPrime : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' v hv
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  exact uloc_le_of_std hW.tr.ok hW.tr.pins.some hJ.is hJ'.is hTr.std a.o.I ha.shape.pre.nodup ha.shape.pre.all j _ _ _ v
    (exists_splitPt hTr.std v hv)

end GlobalTheory.PenLevPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalarStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_bessel_pair_scalar : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) = v) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  first | exact @GlobalTheory.MiTop.centralRatio_stabLoc_atLevel | exact GlobalTheory.MiTop.centralRatio_stabLoc_atLevel | (intros; apply GlobalTheory.MiTop.centralRatio_stabLoc_atLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawCombinationsCompositeNeZeroOfVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawCombinations_composite_ne_zero_of_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (Lp : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (Lp i).q.v) → ∀ g, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) g → g ≠ 0 → (List.finRange n).foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  first | exact @GlobalTheory.CombNonzero.main | exact GlobalTheory.CombNonzero.main | (intros; apply GlobalTheory.CombNonzero.main <;> assumption)
end

