import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamily
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩

open scoped Formalism.L2.Col in

theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = Formalism.L2.Col.lenUW w A B := by
  unfold Formalism.L2.Col.lenUW Formalism.L2.Col.lenW
  rw [Formalism.L2.Col.atW_map, Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j
      rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := GlobalTheory.T.concreteProjector_eq_orthogonalProjection D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ
open scoped ComplexConjugate

namespace GlobalTheory.ZEul

open Classical in

def rsTerm (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

theorem rsTerm_zero (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) : rsTerm q α β x 0 = 1 := by
  have h : (fun _ : Fin n => (0 : ℕ)) = fun i => ((0 : Fin n → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) α = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

def lastRow (g : GA E (m + 1)) : Fin (m + 1) → Ad E := fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j

def uInt (φ φ' : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℂ :=
  whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i))) *
    conj (whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i)))) *
    Φ (fun i => pInf E (lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (lastRow g i)) * (detPow E (m + 1) x g : ℂ)

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WachTensor

noncomputable section

namespace GlobalTheory.NL.BaseField

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}

theorem res_eq_one_iff (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) : W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h1 := W.χΓ_res g
  rw [P.PD_χ] at h1
  constructor
  · intro h
    rw [h, map_one, Units.val_one, map_one] at h1
    exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (h1.symm.trans (map_one _).symm))
  · intro h
    rw [h, Units.val_one, map_one] at h1
    apply W.χΓ_inj
    rw [map_one]
    exact Units.ext (Subtype.ext h1)

theorem ker_transfer {K' : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K')))
    (h : Good K s LL) (h0 : K0 K = K0 K') (g' : ↥(GK K')) (hg : W'.resΓ g' = 1) :
    ∃ g : ↥(GK K), W.resΓ g = 1 ∧ (g : GQ l) = g' :=
  have h1 := (res_eq_one_iff W' g').1 hg
  ⟨⟨g', mem_GK_of_chi P h.2.2.1 h0 g'.2 h1⟩, (res_eq_one_iff W _).2 h1, rfl⟩

theorem sep_of_hausdorff {R : Type} [CommRing R] (a : R) (h : IsHausdorff (Ideal.span {a}) R) (x : R)
    (hx : ∀ k : ℕ, a ^ k ∣ x) : x = 0 :=
  h.haus x fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end Concrete

set_option maxHeartbeats 1600000 in

theorem rings_mem (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (h0 : K0 K = K0 K') :
    (∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a) ∧
      ∀ a, ∃ a', ((F l).E K' s LL h').tie.ioE a' = ((F l).E K s LL h).tie.ioE a := by
  obtain ⟨c1, -, c3, -, c5⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  have h1 : ∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a :=
    io_mem _ _ Subtype.val_injective (descends _) c3 (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.2.2.1
      (fun g' hg' => by
        obtain ⟨g, hg, e⟩ := ker_transfer _ _ h h0 g' hg'
        exact ⟨g, hg, congrArg ((D.locA l).gRW LL) e⟩)
      (sep_of_hausdorff _ (c5 _ (GlobalTheory.Cyc.εroot_sub_one_not_unit (D.locA l) s)).toIsHausdorff)
  refine ⟨h1, ioE_mem _ _ (((D.loc l).PD_p K').trans ((D.loc l).PD_p K).symm) h1 ?_⟩
  rw [(D.loc l).PD_p K]
  exact sep_of_hausdorff _ c1.toIsHausdorff

section Two

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K K' : FinExt l} {s : ℕ} {LL : FinExt l}
  {h : Good K s LL} {h' : Good K' s LL}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  {W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K'))}
  (E : EtSit P AI K s LL h W) (E' : EtSit P AI K' s LL h' W') (T : Lt K LL) (T' : Lt K' LL)

set_option maxHeartbeats 800000 in

theorem jD_mem_sit (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T)
    (he : ∀ (g : ↥(GK K)) (g' : ↥(GK K')), (g : GQ l) = g' → ∀ t, e (T.actT g t) = T'.actT g' (e t))
    (x : W.DD T) : ∃ x', E'.tie.jD T' x' =
      TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) e (E.tie.jD T x) :=
  jD_mem E.tie E'.tie (descends E') (map_ne_top E) (φRW_surjective LL) hE T T' e (fun g' hg' =>
    (ker_transfer W W' h h0 g' hg').imp fun g hg => ⟨hg.1, congrArg (AI.gRW LL) hg.2, he g g' hg.2⟩) x

variable (hle : K.1 ≤ K'.1) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T)
  (hact : ∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t))

include hact in
theorem act_fwd (g' : ↥(GK K')) (g : ↥(GK K)) (e : (g' : GQ l) = g) (t : ↥T'.L.T) :
    eT.toLinearMap (T'.actT g' t) = T.actT g (eT.toLinearMap t) :=
  (hact g' t).trans (congrArg (fun u : ↥(GK K) => T.actT u (eT t)) (Subtype.ext e))

include hact in
theorem act_bwd (g : ↥(GK K)) (g' : ↥(GK K')) (e : (g : GQ l) = g') (t : ↥T.L.T) :
    eT.symm.toLinearMap (T.actT g t) = T'.actT g' (eT.symm.toLinearMap t) := by
  apply eT.injective
  have h1 := act_fwd T T' hle eT hact g' g e.symm (eT.symm t)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 ⊢
  exact h1.symm

set_option maxHeartbeats 800000 in
include hact in
theorem jD_bwd (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x) (x : W.DD T) :
    ∃ x', TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap
      (E'.tie.jD T' x') = E.tie.jD T x :=
  (jD_mem_sit E E' T T' h0 hE eT.symm.toLinearMap (act_bwd T T' hle eT hact) x).imp fun _ hx' =>
    (congrArg (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) hx').trans
      (map_id_symm eT.symm (E.tie.jD T x))

set_option maxHeartbeats 800000 in
include hact in
theorem modules_eq (h0 : K0 K' = K0 K) (a1 : ∀ x, ∃ x', E'.tie.io x' = E.tie.io x)
    (a2 : ∀ x, ∃ x', E.tie.io x' = E'.tie.io x) (e1 : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e2 : ∀ x, ∃ x', E.tie.ioE x' = E'.tie.ioE x) (hQ : E'.tie.io W'.Q = E.tie.io W.Q)
    (hinj : Function.Injective E'.tie.ioE)
    (hb : IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)))
    (h10 : IsCrys (P.PD K') T'.ρ → p10 W' T') :
    (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.tie.jD T') =
      Set.range (E.tie.jD T) ∧ (IsCrys (P.PD K) T.ρ → IsCrys (P.PD K') T'.ρ →
      (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) ''
        (E'.tie.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.tie.jD T '' (W.N T : Set (W.DD T))) := by
  have d1 := jD_mem_sit E' E T' T h0 e2 eT.toLinearMap (act_fwd T T' hle eT hact)
  have d2 := jD_bwd E E' T T' hle eT hact h0.symm e1
  refine ⟨Set.Subset.antisymm ?_ ?_, fun hT hT' => ?_⟩
  · rintro _ ⟨_, ⟨x', rfl⟩, rfl⟩
    exact d1 x'
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := d2 x
    exact ⟨_, ⟨x', rfl⟩, hx'⟩
  · exact (hb hT).elim fun b => N_eq E.tie E'.tie T T' eT hT (h10 hT') b hinj a1 a2 e1 hQ d2 d1
      fun g' => ⟨⟨(g' : GQ l), GK_le hle g'.2⟩, rfl, hact g'⟩

end Two

set_option maxHeartbeats 800000 in

theorem base_indep : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → let W' := (HW l).W K' s LL h'; let E' := ((F l).E K' s LL h').tie; Set.range E.io = Set.range E'.io ∧ Set.range E.ioE = Set.range E'.ioE ∧ ∀ (T : Lt K LL) (T' : Lt K' LL) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T), (∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t)) → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.jD T') = Set.range (E.jD T) ∧ (IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K') T'.ρ → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' (E'.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.jD T '' (W.N T : Set (W.DD T))) := by
  intro D HW F l _ K s LL h W E K' h' hle h0 W' E'
  have a1 := (rings_mem D HW F l K s LL h K' h' h0.symm).1
  have e1 := (rings_mem D HW F l K s LL h K' h' h0.symm).2
  have a2 := (rings_mem D HW F l K' s LL h' K h h0).1
  have e2 := (rings_mem D HW F l K' s LL h' K h h0).2
  have q := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have q1 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.1
  have q2 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.1
  refine ⟨?_, ?_, fun T T' eT hact => ?_⟩
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 a1) (Set.range_subset_iff.2 a2)
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 e1) (Set.range_subset_iff.2 e2)
  have hb := N_basis D HW F l K s LL h T
  have h10 : IsCrys ((D.loc l).PD K') T'.ρ → p10 ((HW l).W K' s LL h') T' := GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K' s LL h' T'
  exact modules_eq ((F l).E K s LL h) ((F l).E K' s LL h') T T' hle eT hact h0 a1 a2 e1 e2 (q1.trans q.symm)
    q2 hb h10

end GlobalTheory.NL.BaseField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCaseStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTorsionClassTheorem_goodCase : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTB.tb_assembled | exact GlobalTheory.TheoremTB.tb_assembled | (intros; apply GlobalTheory.TheoremTB.tb_assembled <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformColumnLaw
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_blkU_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a),
      colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hf y g
  have hper := per_coef (a := a) hψ (eLast a (m + 1)) hf.cont
    (fun c g' => hf.left _ (isMir_blkU c) g') g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast a (m + 1)) y) *
        (ψ (-dot (eLast a (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E a) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast a (m + 1)) y) * ψ (-dot (eLast a (m + 1)) y)) *
            (ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast a (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachLatticeTrivialModUniformizer

set_option maxHeartbeats 1000000 in

theorem wachLattice_galois_trivial_mod_uniformizer : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P2 D HW F := by
  intro D HW F Cm l _ K s LL h T hT
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.NL.GamModX.gam_mod_π_mod_X D HW F Cm l K s LL h T hT
  refine ⟨(wach_gamma_stable_first _ T).1, (wach_gamma_stable_first _ T).2, fun x hx => ?_⟩
  obtain ⟨y, hy, e⟩ := h3 x hx
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.NL.WachLatticeTrivialModUniformizer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotientStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaSemisimpleQuotientD_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | exact GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient <;> assumption)
end

