import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0719
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0720
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0693
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_linForm_cut_face_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  intro O _ bar X _ _ m n p δ γ γ' h₂ h₁ hδb hδp hγ' h2δ h2γ hf2 h1γ h1γ' hf1
  set K : ℤ := 1 + ∑ i, |h₁ (δ i)| with hK
  have hKi : ∀ i, |h₁ (δ i)| < K := fun i => by
    have := Finset.single_le_sum (f := fun i => |h₁ (δ i)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (h₁ (δ i)))
    linarith
  have happ : ∀ x, (K • h₂ + h₁) x = K * h₂ x + h₁ x := fun x => by simp
  have hpos : ∀ i, 0 < h₂ (δ i) → 0 < (K • h₂ + h₁) (δ i) := fun i hi => by
    rw [happ]
    have h1 : K ≤ K * h₂ (δ i) := by nlinarith
    have := neg_abs_le (h₁ (δ i))
    linarith [hKi i]
  have hnn : ∀ i, 0 ≤ (K • h₂ + h₁) (δ i) := fun i => by
    rcases (h2δ i).lt_or_eq with hi | hi
    · exact (hpos i hi).le
    · rw [happ, ← hi, mul_zero, zero_add]
      exact InRCone.apply_nonneg (hf2 _ (hδb i) (hδp i) (inRCone_self δ i) hi.symm) h₁ h1γ
  have h2γ' : ∀ j, h₂ (γ' j) = 0 := fun j => le_antisymm (by
      have := InRCone.apply_nonneg (hγ' j) (-h₂) (fun k => by simp [h2γ k])
      simpa using this)
    (InRCone.apply_nonneg (hγ' j) h₂ (fun k => (h2γ k).ge))
  refine ⟨K • h₂ + h₁, hnn, fun j => by rw [happ, h2γ' j, h1γ' j]; ring, ?_⟩
  intro β hb hp hc hz
  have h2β : h₂ β = 0 := by
    obtain ⟨c, hc0, e⟩ := hc
    have eh := apply_eq_of_toReal_eq e (K • h₂ + h₁)
    have e2 := apply_eq_of_toReal_eq e h₂
    rw [hz, Int.cast_zero] at eh
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ c i * ((K • h₂ + h₁) (δ i) : ℝ) := fun i _ =>
      mul_nonneg (hc0 i) (by exact_mod_cast hnn i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 eh.symm
    have hs : ∑ i, c i * (h₂ (δ i) : ℝ) = 0 := Finset.sum_eq_zero fun i _ => by
      rcases (h2δ i).lt_or_eq with hi | hi
      · have h0 := hall i (Finset.mem_univ _)
        have hp' : (0 : ℝ) < (K • h₂ + h₁) (δ i) := by exact_mod_cast hpos i hi
        rw [(mul_eq_zero.1 h0).resolve_right hp'.ne', zero_mul]
      · rw [← hi]; simp
    exact_mod_cast e2.trans hs
  have hγβ := hf2 β hb hp hc h2β
  refine hf1 β hb hp hγβ ?_
  have := happ β
  rw [hz, h2β] at this
  linarith

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevels
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem mtAd_L {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    ∃ ad : MtAd Y (mtD L l), ad.PV = pvL L l := by
  refine ⟨{ PV := pvL L l
            std := (by with_unfolding_all exact (l.mt.ad.std :))
            eW := (by with_unfolding_all exact (l.mt.ad.eW :))
            read := fun μ h i y g => ?_
            rat := (by with_unfolding_all exact (l.mt.ad.rat :))
            wt := (by with_unfolding_all exact (l.mt.ad.wt :))
            id := (by with_unfolding_all exact (l.mt.ad.id :)) }, rfl⟩
  have h1 := l.mt.ad.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))
  have h2 := hY.jMt μ h i y
  exact (by with_unfolding_all exact (h1.trans (congrFun (eq_of_heq h2) _).symm :))

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisations
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Fin3.MvLoc

section Three

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A : DIV.FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} (R : Links.RealDat3 a.D A Ks)

def thrice : type_of% (real3 c R) := (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thriceY : type_of% (letI := alg c iK; (real3 c R).ioY) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioY :))

def thriceX : type_of% (letI := alg c iK; (real3 c R).ioX) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioX :))

theorem thriceY_eq : letI := alg c iK; (real3 c R).ioY = thriceY b c R := by
  have h1 := real_ioY c R.toRealDat
  have h2 := real_ioY b R.toRealDat
  have h3 := real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceY b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thriceX_eq : letI := alg c iK; (real3 c R).ioX = thriceX b c R := by
  have h1 := real_ioX c R.toRealDat
  have h2 := real_ioX b R.toRealDat
  have h3 := real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceX b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thrice_eq : real3 c R = thrice b c R := by
  letI := alg c iK
  exact (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (real3 c R)) (thriceY_eq b c R) (thriceX_eq b c R)) :))

theorem inertTransport_twice_heq_direct : HEq (real3 (a := b) c (iK := alg b iK) (real3 b R)) (real3 c R) :=
  (by with_unfolding_all exact ((HEq.symm (heq_of_eq (thrice_eq b c R))) :))

end Three

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

theorem coreJ_heq {k₀ : Formalism.L2.Pj.CoreJ a.D} {k : Formalism.L2.Pj.CoreJ b.D} (h : HEq k (coreJ b k₀)) : HEq (coreJ c k) (coreJ c k₀) := by
  obtain rfl : k = coreJ b k₀ := eq_of_heq h
  exact (by with_unfolding_all exact ((HEq.refl (coreJ c k₀)) :))

theorem realAdelicInertTransport_heq_of_transport (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) (k : Formalism.L2.Pj.CoreJ b.D)
    (i : Algebra k.Q.c.F b.D.what₂.LL) (hi : ∀ y : k.Q.c.F, B.embLL (algebraMap k.Q.c.F b.D.what₂.LL y) = (y : ℂ))
    (R : Links.RealDat3 b.D (famR b.st I hX (usedOf I T Wt) Xg tr) k.Q.c.F) (hXg : Xg = z₀.Xg)
    (htr : tr = z₀.tr) (hc : HEq k (coreJ b z₀.core)) (hR : HEq R (real3 b (iK := z₀.alg) z₀.R)) :
    HEq (real3 c (iK := i) R) (real3 c (iK := z₀.alg) z₀.R) := by
  subst hXg htr
  obtain rfl : k = coreJ b z₀.core := eq_of_heq hc
  have ha : i = (by with_unfolding_all exact ((alg b z₀.alg) :)) :=
    Algebra.algebra_ext _ _ fun y => (by with_unfolding_all exact ((B.embLL.injective ((hi y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))) :
      _ = (@algebraMap _ _ _ _ z₀.alg ((by with_unfolding_all exact (y :))) : B.LL)) :))
  subst ha
  have hR' : R = (by with_unfolding_all exact ((real3 b (iK := z₀.alg) z₀.R) :)) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  exact (by with_unfolding_all exact ((inertTransport_twice_heq_direct b c (iK := z₀.alg) z₀.R) :))

end Copy

section Move

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o o' : q.Over}

theorem coreP_transfer {Z Z' : w.Lt} (s : SameGrp (B := B) (C := w.C) Z Z') {z : Dat (w.st Z) w.I hX T Wt} (h : CoreP z) :
    CoreP (w := w) (Z := Z') (Dat.transfer (B := B) (C := w.C) (a := Z) (b := Z') s z) :=
  ⟨(by with_unfolding_all exact ((Mv.lawsCore_tr (a := Z) Z' h.1) :)), (by with_unfolding_all exact (h.2.1 :)), (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩

theorem copy_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) {m : Moved o} {m' : Moved o'} (hm : m.Copy)
    (e : m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z) : m'.Copy := by
  have h1 := coreJ_heq (a := Z₀) o.Z o'.Z (k₀ := z₀.core) (k := m.z.core) ((by with_unfolding_all exact (hm.core :)))
  have h2 := realAdelicInertTransport_heq_of_transport (a := Z₀) o.Z o'.Z z₀ m.z.Xg m.z.tr m.z.core m.z.alg m.z.alg_eq m.z.R m.Xg m.tr ((by with_unfolding_all exact (hm.core :))) ((by with_unfolding_all exact (hm.R :)))
  have e1 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.core) e
  have e2 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.R) e
  have h3 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).core (coreJ (a := Z₀) o'.Z z₀.core) := (by with_unfolding_all exact (h1 :))
  have h4 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).R (real3 (a := Z₀) o'.Z (iK := z₀.alg) z₀.R) := (by with_unfolding_all exact (h2 :))
  exact ⟨(by with_unfolding_all exact ((HEq.trans e1 h3) :)), (by with_unfolding_all exact ((HEq.trans e2 h4) :))⟩

theorem exists_moved_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hm : m.Coh) :
    ∃ m' : Moved o', m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := Mv.pkT_tr (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  have hW := Dat.nonzeroIndexPlaces_transferAlongSameFiniteGroup (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have b2 := HEq.trans hy.PY hm.PY
  have b3 := HEq.trans hy.PW hm.PW
  have b4 := HEq.trans a2 hm.rep
  have b5 := fun c => HEq.trans (a3 c) (hm.jE c)
  have b6 := fun c => HEq.trans (a4 c) (hm.jM c)
  have b7 := fun c => HEq.trans (a5 c) (hm.jX c)
  have b8 := HEq.trans a6 hm.eW
  have b9 := HEq.trans a7 hm.jMt
  have c1 := fun j v => (he j v).trans (m.eta j ((by with_unfolding_all exact (v :))))
  have c2 := fun F0 => (hW F0).symm.trans (m.W1 ((by with_unfolding_all exact (F0 :))))
  have c3 := fun c u => HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c u).j) hA)) (m.tA c u)
  refine ⟨{ z := Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((Dat.holds_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.intersectionNumber_baseChange) :))
            exAt := (by with_unfolding_all exact ((Dat.exAt_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.exAt) :))
            inGeo := (by with_unfolding_all exact ((Dat.inGeo_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => coreP_transfer s (m.core h)
            eta := (by with_unfolding_all exact (c1 :))
            W1 := (by with_unfolding_all exact (c2 :))
            y := (by with_unfolding_all exact ((Mv.hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := (by with_unfolding_all exact (c3 :)) }, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hm.tupT :))
  · exact (by with_unfolding_all exact (b2 :))
  · exact (by with_unfolding_all exact (b3 :))
  · exact (by with_unfolding_all exact (b4 :))
  · exact (by with_unfolding_all exact (b5 :))
  · exact (by with_unfolding_all exact (b6 :))
  · exact (by with_unfolding_all exact (b7 :))
  · exact (by with_unfolding_all exact (b8 :))
  · exact (by with_unfolding_all exact (b9 :))

end Move

theorem exists_moved_loc : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  intro K B f T w P x L
  obtain ⟨m, h1, h2⟩ := exists_moved_transfer (o := x.o) (o' := oL x L) (sameL x L) x.m x.coh
  exact ⟨m, h1, copy_transfer (o := x.o) (o' := oL x L) (sameL x L) x.copy h1, h2⟩

end GlobalTheory.HeightCounting.Fin3.MvLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormElementCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_element_congruence : PrN → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  first | exact @GlobalTheory.HeightCounting.Up.gnorm_allSt | exact GlobalTheory.HeightCounting.Up.gnorm_allSt | (intros; apply GlobalTheory.HeightCounting.Up.gnorm_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniformStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_gridCharacters_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T) (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩, GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  first | exact @GlobalTheory.GridField.exists_field_uniform | exact GlobalTheory.GridField.exists_field_uniform | (intros; apply GlobalTheory.GridField.exists_field_uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPenultimateLevelCouplingCosetsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_penultimateLevel_couplingCosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  first | exact @GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets | exact GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets | (intros; apply GlobalTheory.Mem.Col2.TwistLevel.exists_levJ_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntFormStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d → y ≠ 0 → toReal x = d • toReal y →
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  first | exact @GlobalTheory.posReal_multiple_rat | exact GlobalTheory.posReal_multiple_rat | (intros; apply GlobalTheory.posReal_multiple_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMultStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  first | exact @GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | exact GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | (intros; apply GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem exists_rescale_prim : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  intro O _ _ bar φ X _ _ _ m δ hδ hli
  choose n u hmem hn hu hprim using fun i => exists_prim (bar := bar) (hδ.mem i) (hli.ne_zero i)
  have hcu : IsCell bar φ u := cell_rescale hδ n hn hu hmem
  refine ⟨u, hcu, linearIndependent_of_smul hli n hn hu, fun i => hprim i, ?_⟩
  rintro β ⟨c, hc, hβ⟩
  refine ⟨fun i => c i * n i, fun i => mul_nonneg (hc i) (Nat.cast_nonneg _), ?_⟩
  rw [hβ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : toReal (δ i) = (n i : ℝ) • toReal (u i) := by
    rw [hu i]; exact LinearMap.ext₂ fun x y => by simp
  rw [e, smul_smul]

end GlobalTheory.PolFan.SmoothEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowFormsAdelicDecoratedLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowsRead

theorem decoPt_eq_decoAd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι} (t : TupU I U)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) (hc : CMData X.B.fields.F X.B.fields.E)
    (h : Bridge.Gf X.toD7.sp.X') (x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1))
    (hM : MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1)) :
    Formalism.L2.Col.decoPt hc (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk x) =
      GlobalTheory.Mem.R3.RowAd.decoAd X I t h := by
  have hx : x.1 = GlobalTheory.Mem.R3.RowAd.ptE X h := by
    ext i j
    have := hM.2 (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i) (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j) i j rfl rfl
    rw [hβ, matIn, mul_one] at this
    exact this.symm
  rw [Formalism.L2.Col.decoPt_mk, hx]
  rfl

theorem exists_matEq_ptE (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) :
    ∃ hc : CMData X.B.fields.F X.B.fields.E, ∀ h : Bridge.Gf X.toD7.sp.X', ∃ x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1),
      MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1) := by
  refine ⟨X.toD7.sp.cm, fun h => ⟨⟨GlobalTheory.Mem.R3.RowAd.ptE X h, GlobalTheory.Mem.R3.RowDeco.ptE_mem_UAd X I hI h⟩, GlobalTheory.Mem.R3.RowAd.rank_X' X, ?_⟩⟩
  intro i j i' j' hi hj
  obtain rfl : i = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i' := Fin.ext hi
  obtain rfl : j = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j' := Fin.ext hj
  rw [hβ, matIn, mul_one]
  rfl

set_option maxHeartbeats 4000000 in

theorem exists_rowSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ _
  obtain ⟨c, -, hli, -, -, hcI, hP⟩ := GlobalTheory.Mem.R3.RowStd.exists_std_wtCast X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ
  choose P hPr hCo using hP
  have hRd : ∀ t, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t (P t) := fun t => ⟨c, hPr t⟩
  choose a ha using fun t => GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)
  refine ⟨fun t => { pres := P t, act_tie := a t, hecke := (GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)).some },
    fun t => ⟨ha t, hCo t, GlobalTheory.Mem.R3.RowAd.Inert.exists_inertTie X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)⟩, c, hcI, ?_, hli, exists_matEq_ptE X I hI L hβ⟩
  intro hc t φ h x hM
  refine (hPr t _ h).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun d => c (φ.2.1 d)) (decoPt_eq_decoAd X I t L hβ hc h x hM).symm

end GlobalTheory.Mem.R3.RowsRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicatorStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_presentation_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ p : ℕ, p.Prime → (∃ ζ : A, IsPrimitiveRoot ζ p) → SplitTors t x₀ p → ∃ (n : ℕ) (h : Fin n → Fin g → A), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* ↥(intO C)), (∀ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), ∃ j, DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) ∧ ∀ j, ∃ c : TorsChar t (spMap x ≫ x₀) (p ^ 1), DlogIs t p 1 c (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i)) := by
  first | exact @GlobalTheory.HTMap.hodgeTate_map | exact GlobalTheory.HTMap.hodgeTate_map | (intros; apply GlobalTheory.HTMap.hodgeTate_map <;> assumption)
end

