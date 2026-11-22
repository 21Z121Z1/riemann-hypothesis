import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Imports
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Bundle0003
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThIndEqAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.CharacterFactorUnitaryAction
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdeal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.GMConjTranspose

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColDatK
section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)

theorem embT_ofRec : Cd.TaylorLogMetric.embT (Car.ofRec D) = TaylorLogMetric.embT D := rfl

theorem lamOf_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.lamOf (Car.ofRec D) cc δ = TaylorLogMetric.lamOf D cc δ := rfl

theorem La_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.La (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) L L' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := rfl

theorem Iop_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (G : TaylorLogMetric.VC D N N' → ℂ) :
    Cd.TaylorLogMetric.Iop (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) La₁ La₂ G = TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) La₁ La₂ G := rfl

theorem isCurveIdeal_ofRec (cc : Ideal (𝓞 D.host.K)) : Cd.TaylorLogMetric.IsCurveIdeal (Car.ofRec D) cc ↔ TaylorLogMetric.IsCurveIdeal D cc := Iff.rfl

theorem isTwelfthRootDisc_ofData_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Car.ofRec D) cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl

theorem isChi_ofRec (χ : TaylorLogMetric.IdE D → ℂ) : Cd.TaylorLogMetric.IsChi (Car.ofRec D) χ ↔ TaylorLogMetric.IsChi D χ := Iff.rfl

theorem admissible_ofData_iff {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.admitted (Car.ofRec D) N N' L L' ↔ TaylorLogMetric.admitted D N N' L L' := Iff.rfl

theorem isDgen_ofRec (cD : D.what₂.Tau → ℂ) : Cd.IsDgen (Car.ofRec D) cD ↔ IsDgen D cD := Iff.rfl

variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

def KapChoice.ofCar {γ₀ : IsoK D} (k : Cd.KapChoice (D := Car.ofRec D) γ₀) : KapChoice γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

def Base.ofCar (B : Cd.Base (Car.ofRec D) cc δ) : Base D cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := KapChoice.ofCar B.kc

theorem Base.ofCar_toCar (B : Base D cc δ) : Base.ofCar B.toCar = B := rfl

theorem Base.toCar_ofCar (B : Cd.Base (Car.ofRec D) cc δ) : (Base.ofCar B).toCar = B := rfl

theorem Base.kappa_toCar (B : Base D cc δ) : B.toCar.kappa = B.kappa := rfl

theorem Base.stdOK_toCar (B : Base D cc δ) : B.toCar.StdOK ↔ B.StdOK := Iff.rfl

theorem Base.thMM_toCar (B : Base D cc δ) : B.toCar.thMM = B.thMM := rfl

theorem Base.thMoved_toCar (B : Base D cc δ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : B.toCar.thMoved N N' L L' = B.thMoved N N' L L' := rfl

theorem chiFac_ofRec (χ : TaylorLogMetric.IdE D → ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.Base.chiFac (D := Car.ofRec D) χ N N' L L' = Base.chiFac χ N N' L L' := rfl

theorem Base.eNat_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.eNat χ = B.eNat χ := rfl

theorem Base.eqP_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.EqP χ ↔ B.EqP χ := Iff.rfl

variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

def Seam.ofCar (s : Cd.Seam (Car.ofRec D) X) : Seam D X := ⟨s.iE, s.iT, s.σ₀⟩

theorem Seam.ok_toCar (s : Seam D X) : s.toCar.Ok ↔ s.Ok := Iff.rfl

theorem ambOf_toCar (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    Cd.ambOf s.toCar B.toCar χ cD = ambOf s B χ cD := rfl

theorem ambOf_ofCar (s : Cd.Seam (Car.ofRec D) X) (B : Cd.Base (Car.ofRec D) cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf (Seam.ofCar s) (Base.ofCar B) χ cD = Cd.ambOf s B χ cD := rfl

end Bridge

section OverColDat

variable (d : ColDat)

theorem curve_delta_ne (K : CurveDat d.host d.what₂.embLL d.eTau) : K.δ ≠ 0 := by
  intro h
  have h1 := K.delta_pow_twelve_eq_discr
  rw [h, zero_pow (by norm_num)] at h1
  exact Cd.IntegralLatticeDensity.discrNe (carD d) d.host.ccK d.host.ccK_ne_bot h1.symm

theorem ambIn_nonempty (K : CurveDat d.host d.what₂.embLL d.eTau) (χ : Cd.TaylorLogMetric.IdE (carD d) → ℂ) :
    ∃ I : AmbIn d, I.K = K ∧ I.χ = χ := by
  obtain ⟨B⟩ := Cd.baseExists (carD d) d.host.ccK (Cd.isCurveIdeal_ccK (carD d)) K.δ (curve_delta_ne d K)
  exact ⟨⟨K, B, χ⟩, rfl, rfl⟩

variable {d}

theorem AmbIn.ok_of (I : AmbIn d) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) : I.Ok :=
  ⟨I.B.stdOK (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc, hχ⟩

theorem AmbIn.isDgen (I : AmbIn d) (hM : ∀ τ x, Cd.TaylorLogMetric.embT (carD d) τ x ∈ I.K.M) : Cd.IsDgen (carD d) I.cD :=
  ⟨I.K.M, I.K.nf, hM, fun τ => ⟨I.K.fr τ, rfl, I.K.gen τ⟩⟩

theorem ambIn_ok_nonempty (d : ColDat) (K : CurveDat d.host d.what₂.embLL d.eTau) : ∃ I : AmbIn d, I.K = K ∧ I.Ok := by
  obtain ⟨χ, hχ⟩ := Cd.IntegralLatticeDensity.exists_chi (carD d)
  obtain ⟨I, hK, hI⟩ := ambIn_nonempty d K χ
  exact ⟨I, hK, I.ok_of (hI ▸ hχ)⟩

theorem AmbIn.eqP (I : AmbIn d) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) : I.B.EqP I.χ :=
  Cd.PairingIndexBounds.Eq.SqG.eqP_car I.B (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc I.χ hχ

theorem repN_sd (u : d.Pr.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : IsSdLat (repN (Pr := d.Pr) d.W d.lev u i c) :=
  ⟨((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.lat, ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.uni⟩

set_option maxHeartbeats 1600000 in

theorem AmbIn.xiHyp (I : AmbIn d) (h : d.what₂.embLL.comp d.embE = d.host.φ₀) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) (S : Set ℕ)
    (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E) {n m2 : ℕ} (hm : d.R.m = m2 + 2) (G : ChainGlob (Pr := d.Pr) d.W d.σ₀)
    (rat : ∀ u i, i < d.R.m → I.amb.JetsRat (d.R.N i) (d.R.N (i + 1)) (Sall (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) u)
      (cAof (selD d) _ (cstD d S m0 n) * cBof (selD d) _ (cstD d S m0 n) u))
    (rho : ∀ u, RhoScal (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) G I.amb u) (u : d.Pr.Word) :
    XiHyp (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) I.amb u
      (refXi1 d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) (idxD d S m2) (qe_one (selD d)) m2 (alD d S m2) u) G :=
  xiHypD d S m0 hm G I.amb rfl (fun i _ => I.eSmooth h i (i + 1)) rat
    (fun u i _ c c' => I.chiF_ne h hχ i (i + 1) (repN_sd u i c) (repN_sd u (i + 1) c')) rho u

theorem seamD_lat {n : ℕ} (N : Submodule (𝓞 d.X.E) (Sp d.X.E n)) : (seamD d).lat N = N := by
  ext y
  rw [Cd.Seam.mem_lat]
  exact ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun h => ⟨y, h, rfl⟩⟩

theorem AmbIn.amb_e (I : AmbIn d) (a b : ℕ) (N : Submodule (𝓞 d.X.E) (Sp d.X.E a)) (N' : Submodule (𝓞 d.X.E) (Sp d.X.E b)) :
    I.amb.e a b N N' = I.B.eNat I.χ a b N N' := by
  have h : I.amb.e a b N N' = I.B.eNat I.χ a b ((seamD d).lat N) ((seamD d).lat N') := rfl
  rw [h, seamD_lat, seamD_lat]

theorem AmbIn.amb_sig (I : AmbIn d) : I.amb.σ₀ = d.σ₀ := rfl

theorem AmbIn.amb_cD (I : AmbIn d) : I.amb.cD = I.cD := rfl

def Car.ofColRec (c : ColRec) : Car := ⟨c.R, c.host, ⟨c.what₂.Tau, c.what₂.card_Tau⟩, c.eTau⟩

theorem car_of_colRec (D : D7) (d : ColDat) (a : ColArgs d) (h : D.colRec = d.colRec a) : Car.ofRec D = carD d :=
  congrArg Car.ofColRec h

end OverColDat

theorem Cd.exists_base_ne (D : Car) : ∃ (δ : ℂ) (B : Cd.Base D D.host.ccK δ), Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ B.StdOK ∧
    ∀ N N' L L', Cd.TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' ≠ 0 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Cd.TaylorLogMetric.lamOf D D.host.ccK 1)) (by norm_num : 0 < 12)
  have h0 := Cd.twelfth_root_disc_ne_zero D D.host.ccK D.host.ccK_ne_bot hδ
  obtain ⟨B⟩ := Cd.baseExists D D.host.ccK (Cd.isCurveIdeal_ccK D) δ h0
  have hS := B.stdOK (Cd.isCurveIdeal_ccK D) hδ
  exact ⟨δ, B, hδ, hS, fun N N' L L' hA =>
    B.thMoved_ne_zero hS (B.latAll (Cd.isCurveIdeal_ccK D) hδ h0) (B.thZeroMem hS N N') hA⟩

namespace Test

open Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits

def exampleCMData : Car := ⟨R0, H0, ⟨R0.Psi, by rw [card_Psi]; rfl⟩, Equiv.refl _⟩

theorem moved_vacuum_ne_zero_example : ∃ (δ : ℂ) (B : Cd.Base exampleCMData exampleCMData.host.ccK δ),
    B.thMoved 2 4 (Cd.StandardLatticesGL3.stdL exampleCMData 2) (Cd.StandardLatticesGL3.stdL exampleCMData 4) ≠ 0 := by
  obtain ⟨δ, B, -, -, h⟩ := Cd.exists_base_ne exampleCMData
  exact ⟨δ, B, h 2 4 _ _ (Cd.Inhab.Adm_std exampleCMData 2 4 (by decide) (by decide))⟩

end Test

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkConj
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd.CarC

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : Car} {X : Fields} (s : Cd.Seam D X)

def matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

theorem vec_gmap {n : ℕ} (γ : UF X.E n) (x : Sp X.E n) : s.vec (γ.1 x) = (matU s γ).mulVec (s.vec x) := by
  have h := toGLm_mulVec γ.1 x
  rw [← h]
  funext i
  simp only [Cd.Seam.vec, Matrix.mulVec, dotProduct, map_sum, map_mul, matU]
  rfl

theorem lat_gmap {n : ℕ} (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (gmap γ.1 N) = SDLat.smulLat (matU s γ) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  simp only [SDLat.smulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact ⟨s.vec x0, (s.mem_lat N _).2 ⟨x0, hx0, rfl⟩, (vec_gmap s γ x0).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    exact ⟨γ.1 x0, ⟨x0, hx0, rfl⟩, vec_gmap s γ x0⟩

theorem matU_mem (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    (letI := D.host.cmStar; matU s γ ∈ Matrix.unitaryGroup (Fin n) D.host.E) := by
  let _ := D.host.cmStar
  have h : Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) * 1 *
      ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ γ
  rw [Matrix.mul_one] at h
  have key : star (matU s γ) = (Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)).map s.iE := by
    ext i j
    rw [Matrix.star_apply, Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj]
    simp only [matU, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    rw [hok.2]
  rw [Matrix.mem_unitaryGroup_iff', key, matU, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem det_matU {n : ℕ} (γ : UF X.E n) : (matU s γ).det = s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := by
  rw [← TE.det_ufGL]
  exact (RingHom.map_det s.iE.toRingHom _).symm

theorem prod_emb (hok : s.Ok) (z : X.E) : ∏ τ : X.Tau, X.embC s.σ₀ τ z = ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (s.iE z) :=
  Fintype.prod_equiv s.iT _ _ fun τ => hok.1 τ z

end SeamU

section Laws

variable {D : Car} {X : Fields} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem ambOf_conj (hok : s.Ok) (τ : X.Tau) (x : X.E) :
    X.embC (Cd.ambOf s B χ cD).σ₀ τ (star x) = star (X.embC (Cd.ambOf s B χ cD).σ₀ τ x) := by
  let _ := D.host.cmStar
  show s.σ₀ (X.emb τ (star x)) = star (s.σ₀ (X.emb τ x))
  rw [hok.1, hok.1, hok.2, ← Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star']

theorem chiLaw_ambOf_of (hok : s.Ok) (hχ : Cd.TaylorLogMetric.IsChi D χ) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).ChiLaw a b := by
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN'
  show Cd.Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) = _ * _ * Cd.Base.chiFac χ a b (s.lat N) (s.lat N')
  rw [lat_gmap, lat_gmap]
  have h := Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.character_factor_unitary_action χ hχ (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.detSmul D) (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.norm_one_unit_ideal D) ha hb (s.lat N) (s.lat N')
    ⟨matU s γ, matU_mem s hok γ⟩ ⟨matU s γ', matU_mem s hok γ'⟩ (s.sd_lat hok hN) (s.sd_lat hok hN')
  simp only at h
  rw [h]
  have u1 := Matrix.det_of_mem_unitary (matU_mem s hok γ)
  have p1 : ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (star (matU s γ).det) = (∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ := by
    rw [prod_emb s hok, ← Finset.prod_inv_distrib, ← det_matU]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  have p2 : ∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (matU s γ').det = ∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := by
    rw [prod_emb s hok, ← det_matU]
  show Cd.Base.chiFac χ a b (s.lat N) (s.lat N') * ((∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (star (matU s γ).det)) ^ (b / 2) *
      (∏ τ : D.what₂.Tau, Cd.TaylorLogMetric.embT D τ (matU s γ').det) ^ (a / 2)) = _
  rw [p1, p2, inv_pow, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
  rfl

theorem chiLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).ChiLaw a b :=
  chiLaw_ambOf_of s B χ cD hN.2.2.2.2.2.1 hN.2.2.2.1 ha hb

theorem eNat_analytic (hθ : AnalyticOnNhd ℂ B.thMM Set.univ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have hT := entireStatements_holds
  have h0 : AnalyticOnNhd ℂ (B.thZero N N') Set.univ := hT.2 _ B.thMM N N' hθ
  have h1 : AnalyticOnNhd ℂ (B.thHalf N N' L) Set.univ := hT.1 _ _ _ _ _ _ _ _ h0
  have h2 : AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ := hT.1 _ _ _ _ _ _ _ _ h1
  intro z _
  exact analyticAt_const.mul (h2 z (Set.mem_univ _))

theorem eOmega_ambOf_of (hS : B.StdOK) (a b : ℕ) : (Cd.ambOf s B χ cD : Amb X).EOmega a b := by
  intro N N' _ _
  have hA := eNat_analytic B χ (B.thMM_spec hS).1.1 a b (s.lat N) (s.lat N')
  have hc : ContDiff ℂ ⊤ (B.eNat χ a b (s.lat N) (s.lat N')) := hA.contDiff
  exact hc.comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))

theorem eOmega_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) (a b : ℕ) : (Cd.ambOf s B χ cD : Amb X).EOmega a b :=
  eOmega_ambOf_of s B χ cD (B.stdOK hN.1 hN.2.1) a b

theorem eqLaw_ambOf_of (hok : s.Ok) (hE : B.EqP χ) {a b : ℕ} (ha : Even a) (hb : Even b) : (Cd.ambOf s B χ cD : Amb X).EqLaw a b := by
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN' z
  have hE1 := hE.1 a b ⟨s.lat N, s.sd_lat hok hN⟩ ⟨s.lat N', s.sd_lat hok hN'⟩ ha hb ⟨matU s γ, matU_mem s hok γ⟩ ⟨matU s γ', matU_mem s hok γ'⟩
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (Cd.ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [lat_gmap, lat_gmap]
  have hE' := congrFun hE1 (fun τ => z (s.iT.symm τ))
  rw [← hE']
  unfold Cd.TaylorLogMetric.pull
  congr 1
  funext τ i j
  obtain ⟨τ', rfl⟩ := s.iT.surjective τ
  simp only [Equiv.symm_apply_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold Amb.pullV
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : ∀ y : X.E, Cd.TaylorLogMetric.embT D (s.iT τ') (s.iE y) = X.embC s.σ₀ τ' y := fun y => (hok.1 τ' y).symm
  have f1 : star ((B.tor).emb (s.iT τ') (matU s γ' k i)) = X.embC s.σ₀ τ' (γ'.1.symm (Pi.single k 1) i) := by
    rw [TE.ufInv_apply, matU, Matrix.map_apply, TE.ufGL_apply']
    show star (Cd.TaylorLogMetric.embT D (s.iT τ') (s.iE _)) = _
    rw [← Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star', Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, ← hok.2, e1]
  have f2 : (B.tor).emb (s.iT τ') (matU s γ l j) = X.embC s.σ₀ τ' (γ.1 (Pi.single j 1) l) := by
    rw [matU, Matrix.map_apply, TE.ufGL_apply']
    exact e1 _
  rw [f1, f2]
  rfl

theorem eqLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : Cd.NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (Cd.ambOf s B χ cD : Amb X).EqLaw a b :=
  eqLaw_ambOf_of s B χ cD hN.2.2.2.2.2.1 (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG.eqP_car B hN.1 hN.2.1 χ hN.2.2.2.1) ha hb

end Laws

end Formalism.L2.Ker.Cd.CarC
end
end

