import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0010
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0011
import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColLoc
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0005
import Formalism.GL3MeanSquares.HookFormulaTorsion.HadamardUnitDiagonalDetLeOne

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.MapIntRatComplex
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def dpowR (R : Type) [CommRing R] (n c : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  lpMinor R (r := n) (n := n) n le_rfl le_rfl ^ c

theorem map_dpowR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n c : ℕ) :
    map φ (dpowR R n c) = dpowR S n c := by
  unfold dpowR
  rw [map_pow, lclosedeq_lpMinor_map]

theorem twist_mem_gen (R : Type) [CommRing R] {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) :
    ∀ v ∈ weyl R n n le_rfl sg.natW, dpowR R n sg.detShift.toNat * v ∈ weyl R n n le_rfl (sgNat sg) := by
  rw [sgNat_eq lt sg h0 hI]
  cases n with
  | zero =>
    have hc : sg.detShift.toNat = 0 := by unfold DomWeight.detShift; simp
    have hf : (fun i : Fin 0 => sg.natW i + 0) = sg.natW := funext fun i => i.elim0
    simp only [hc, hf]
    simp [dpowR]
  | succ m => exact fun v hv => det_mul_mem_weyl R sg.natW _ v hv

theorem weylQ_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (x : MvPolynomial (Fin r × Fin n) ℚ)
    (hx : x ∈ weyl ℚ r n hn ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ y ∈ weyl ℤ r n hn ν, (N : ℚ) • x = map (Int.castRingHom ℚ) y := by
  unfold weyl at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [Int.cast_one, one_smul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1, y1, hy1, e1⟩ := ihx
    obtain ⟨N2, h2, y2, hy2, e2⟩ := ihy
    refine ⟨N1 * N2, mul_ne_zero h1 h2, N2 • y1 + N1 • y2,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hy2), ?_⟩
    rw [map_add, map_smul_gen, map_smul_gen, ← e1, ← e2, smul_add, smul_smul, smul_smul, eq_intCast, eq_intCast,
      Int.cast_mul, mul_comm (N2 : ℚ)]
  | smul c x _ ihx =>
    obtain ⟨N1, h1, y1, hy1, e1⟩ := ihx
    refine ⟨(c.den : ℤ) * N1, mul_ne_zero (by exact_mod_cast c.den_ne_zero) h1, c.num • y1,
      Submodule.smul_mem _ _ hy1, ?_⟩
    rw [map_smul_gen, ← e1, smul_smul, smul_smul, eq_intCast]
    congr 1
    have := Rat.den_mul_eq_num c
    push_cast
    rw [← this]
    ring

theorem nablaZ_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (q : MvPolynomial (Fin r × Fin n) ℤ)
    (hq : q ∈ dualWeyl ℤ r n ν) : ∃ N : ℤ, N ≠ 0 ∧ N • q ∈ weyl ℤ r n hn ν := by
  have h1 : map (Int.castRingHom ℚ) q ∈ weyl ℚ r n hn ν := by
    rw [Formalism.GradedWeylDivisibility.weylEqNablaQ r n hn ν hν]
    exact Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ r n ν q hq
  obtain ⟨N, hN, y, hy, e⟩ := weylQ_denom hn ν _ h1
  refine ⟨N, hN, ?_⟩
  have : N • q = y := by
    apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_smul_gen, eq_intCast, e]
  rw [this]
  exact hy

def fockQLin {κ : Type} (G : MvPolynomial κ ℚ) : MvPolynomial κ ℚ →ₗ[ℚ] ℚ where
  toFun F := fockQ F G
  map_add' F F' := (Formalism.GradedWeylDivisibility.fockQBilin κ F F' G 0).1
  map_smul' c F := by rw [(Formalism.GradedWeylDivisibility.fockQBilin κ F 0 G c).2, smul_eq_mul, RingHom.id_apply]

theorem fockQ_comm {κ : Type} (f g : MvPolynomial κ ℚ) : fockQ f g = fockQ g f := (Formalism.GradedWeylDivisibility.fockQPos κ f g).1

theorem rieszQ {κ : Type} (V : Submodule ℚ (MvPolynomial κ ℚ)) [FiniteDimensional ℚ V] (φ : V →ₗ[ℚ] ℚ) :
    ∃ p ∈ V, ∀ v : V, fockQ p (v : MvPolynomial κ ℚ) = φ v := by
  let B : V →ₗ[ℚ] Module.Dual ℚ V :=
    { toFun := fun x => (fockQLin (x : MvPolynomial κ ℚ)).comp V.subtype
      map_add' := by
        intro x y
        ext v
        show fockQ (v : MvPolynomial κ ℚ) ((x : MvPolynomial κ ℚ) + y) = fockQ (v : MvPolynomial κ ℚ) x + fockQ (v : MvPolynomial κ ℚ) y
        rw [fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ _ _ 0).1, fockQ_comm, fockQ_comm (y : MvPolynomial κ ℚ)]
      map_smul' := by
        intro c x
        ext v
        show fockQ (v : MvPolynomial κ ℚ) (c • (x : MvPolynomial κ ℚ)) = c * fockQ (v : MvPolynomial κ ℚ) x
        rw [fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ 0 _ c).2, fockQ_comm] }
  have hB : ∀ x v : V, B x v = fockQ (v : MvPolynomial κ ℚ) (x : MvPolynomial κ ℚ) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hne' : (x : MvPolynomial κ ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (Formalism.GradedWeylDivisibility.fockQPos κ (x : MvPolynomial κ ℚ) x).2 hne'
    have : B x x = 0 := by rw [hx]; rfl
    rw [hB] at this
    exact hpos.ne' this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨p, hp⟩ := hsurj φ
  refine ⟨p, p.2, fun v => ?_⟩
  rw [← hp, hB, fockQ_comm]

theorem fockQ_hw_pos {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < fockQ (hw ℚ hn ν) (hw ℚ hn ν) :=
  (Formalism.GradedWeylDivisibility.fockQPos _ _ (hw ℚ hn ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ r n hn ν)

theorem intQ_apply (r n : ℕ) (q : MvPolynomial (Fin r × Fin n) ℤ) : intQ r n q = map (Int.castRingHom ℚ) q := rfl

theorem map_int_rat_complex {κ : Type} (g : MvPolynomial κ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [map_map]
  congr 1

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PColFin
section
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_eq_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p = actP lam g p := by
  unfold actAll actP detTwK detPow trAct Formalism.GradedWeylDivisibility.blockAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

def rhoEquiv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam ≃ₗ[K] VV K lam :=
  LinearEquiv.ofLinearMap (rhoK lam g) (rhoK lam g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rhoEquiv_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) : rhoEquiv lam g y = rhoK lam g y := rfl

theorem rhoEquiv_symm_coe (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) :
    (((rhoEquiv lam g).symm y : VV K lam) : Pol K ι n) =
      actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)⁻¹) (y : Pol K ι n) := by
  show actP lam g⁻¹ (y : Pol K ι n) = _
  rw [← actAll_eq_actP]
  congr 1
  funext τ
  simp

theorem mem_span_subtype {P : Type} [AddCommGroup P] [Module K P] (R : Subring K) (U : Submodule K P) {J : Type} (b : J → U) (y : U) :
    y ∈ Submodule.span R (Set.range b) ↔ (y : P) ∈ Submodule.span R (Set.range fun i => (b i : P)) := by
  have h : (Submodule.span R (Set.range b)).map (U.subtype.restrictScalars R) =
      Submodule.span R (Set.range fun i => (b i : P)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h]
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]

end Alg

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_twist (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (Φ : Cl → (W ≃ₗ[K] W)) :
    ⇑(sumBasis (coE.trans (LinearEquiv.piCongrRight fun c => (Φ c).symm)) BK) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (Φ j.2 (BK j.1))) := by
  funext ⟨i, c⟩
  rw [sumBasis_apply]
  show coE.symm ((LinearEquiv.piCongrRight fun c => (Φ c).symm).symm (Pi.single c (BK i))) = _
  congr 1
  funext c'
  show (Φ c').symm.symm ((Pi.single c (BK i) : Cl → W) c') = _
  by_cases h : c' = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end Gen

section Rec

variable {D : D7}

theorem exists_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ} (e : Q.ι ≃ Fin n) :
    ∃ γ, LocBasis D w Q e γ := by
  classical
  have hn : Module.finrank D.what₂.LL Q.V = n := by
    rw [Module.finrank_eq_card_basis Q.b, Fintype.card_congr e, Fintype.card_fin]
  obtain ⟨bK, hbK⟩ := exists_basis_locP (D.plEq w) hQ.2.1 hQ.2.2 hn
  refine ⟨(Q.b.reindex e).toMatrix bK, ?_, ?_⟩
  · have := (Q.b.reindex e).isUnit_det bK
    rwa [Basis.det_apply] at this
  · have hfam : (fun a : Fin n => ∑ i, (Q.b.reindex e).toMatrix bK i a • Q.b (e.symm i)) = bK := by
      funext a
      have := (Q.b.reindex e).sum_repr (bK a)
      simpa [Basis.toMatrix_apply, Basis.reindex_apply] using this
    rw [hfam]
    ext x
    rw [← mem_localization_iff_localizationAtPlace, ← hbK, mem_localization_latticeOf_iff]

theorem localization_eq_of_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) {n : ℕ} (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) (h : LocBasis D w Q e γ) :
    localization₂ (D.plEq w).asIdeal Q.L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i)) := by
  ext x
  rw [mem_localization_iff_localizationAtPlace, h.2, mem_localization_latticeOf_iff]

variable {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def coL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearMap.pi fun c => LinearMap.codRestrict (VV D.what₂.LL ((D.fm u).lam 0)) ((LinearMap.proj c).comp CV.co)
    (fun x => hTV ▸ ((CV.co_range _).1 ⟨x, rfl⟩ c))

theorem coL_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coL CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

theorem coL_bijective : Function.Bijective (coL CV hTV) := by
  constructor
  · intro x y h
    apply CV.co_inj
    funext c
    exact congrArg Subtype.val (congrFun h c)
  · intro F
    obtain ⟨x, hx⟩ := (CV.co_range (fun c => ((F c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)))).2
      (fun c => hTV.symm ▸ (F c).2)
    refine ⟨x, ?_⟩
    funext c
    apply Subtype.ext
    rw [coL_coe, hx]

def coE : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearEquiv.ofBijective (coL CV hTV) (coL_bijective CV hTV)

theorem coE_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coE CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

open Classical in

theorem localization_lattice_eq (Z : ZBasis ((D.fm u).lam 0)) (w : D.what₂.places.Pl)
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ c τ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) :
    localization₂ (D.plEq w).asIdeal ((D.fm u).lat 0).L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun j : Z.J0 × (D.mem u).C.cls 0 =>
        (coE CV hTV).symm (Pi.single j.2 (rhoK ((D.fm u).lam 0) (g j.2) (Z.basis D.what₂.LL j.1)))) := by
  ext x
  have hf := sumBasis_twist (coE CV hTV) (Z.basis D.what₂.LL) (fun c => rhoEquiv ((D.fm u).lam 0) (g c))
  simp only [rhoEquiv_apply] at hf
  rw [mem_localization_iff_localizationAtPlace, CV.fin w (fun c τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) hg x,
    mem_localization_latticeOf_iff, ← hf, mem_span_sumBasis]
  refine forall_congr' fun c => ?_
  rw [mem_span_subtype, mem_intSpanAt_iff w _ Z]
  have h1 : (fun i => ((Z.basis D.what₂.LL i : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0))) =
      fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) := funext fun i => Z.basis_coe D.what₂.LL i
  rw [h1]
  have h2 : ((((coE CV hTV).trans (LinearEquiv.piCongrRight fun c => (rhoEquiv ((D.fm u).lam 0) (g c)).symm)) x c :
      VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) =
      actAll ((D.fm u).lam 0) (fun τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) (CV.co x c) :=
    rhoEquiv_symm_coe _ _ _
  rw [h2]

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordQ
section
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

def incl (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin n)

theorem incl_apply (n : ℕ) (m : Fin n → 𝓞 E) (i : Fin n) : incl n m i = (m i : E) := rfl

theorem incl_injective (n : ℕ) : Function.Injective (incl (E := E) n) := by
  intro a b h
  funext i
  exact RingOfIntegers.coe_injective (congrFun h i)

def psi {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
  ((Matrix.mulVecLin G⁻¹).restrictScalars (𝓞 E)).comp (incl n)

theorem psi_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (m : Fin n → 𝓞 E) : psi G m = G⁻¹ *ᵥ incl n m := rfl

theorem incl_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (m : Fin n → 𝓞 E) :
    incl n (Gm *ᵥ m) = (Gm.map ((↑) : 𝓞 E → E)) *ᵥ incl n m := by
  funext i
  rw [incl_apply]
  exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) Gm m i)

theorem psi_mulVec {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0)
    (m : Fin n → 𝓞 E) : psi (Gm.map ((↑) : 𝓞 E → E)) (Gm *ᵥ m) = incl n m := by
  rw [psi_apply, incl_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

theorem psi_injective {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hdet : G.det ≠ 0) : Function.Injective (psi G) := by
  intro a b h
  apply incl_injective n
  have := congrArg (fun z ↦ G *ᵥ z) h
  simp only [psi_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec] at this
  exact this

theorem det_map_ne {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    Gm.det ≠ 0 := by
  intro h
  apply hdet
  rw [show (Gm.map ((↑) : 𝓞 E → E)) = (algebraMap (𝓞 E) E).mapMatrix Gm from rfl, ← RingHom.map_det, h, map_zero]

theorem card_quot {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E)) (h : Gm.det ≠ 0) :
    Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) = (Algebra.norm ℤ Gm.det).natAbs := by
  have hinj : Function.Injective (Matrix.mulVecLin Gm) := fun a b hab ↦ by
    have : Gm *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hab
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero h this)
  set N : Submodule ℤ (Fin n → 𝓞 E) := (LinearMap.range (Matrix.mulVecLin Gm)).restrictScalars ℤ with hN
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] N := (LinearEquiv.ofInjective (Matrix.mulVecLin Gm) hinj).restrictScalars ℤ
  have key := Submodule.natAbs_det_equiv N e
  have hq : Nat.card ((Fin n → 𝓞 E) ⧸ N) = Nat.card ((Fin n → 𝓞 E) ⧸ LinearMap.range (Matrix.mulVecLin Gm)) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (Matrix.mulVecLin Gm))).toEquiv
  rw [← hq, ← key]
  have hmap : (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → 𝓞 E) →+ N)) =
      (Matrix.mulVecLin Gm).restrictScalars ℤ := by
    ext x
    rfl
  rw [hmap, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

variable {E : Type} [Field E] [NumberField E]

abbrev P0 (n : ℕ) : Submodule (𝓞 E) (Fin n → E) := LinearMap.range (incl (E := E) n)

def Between {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {C | P0 n ≤ C ∧ C ≤ LinearMap.range (psi G) ∧ C.FG}

theorem between_finite_card {n : ℕ} (Gm : Matrix (Fin n) (Fin n) (𝓞 E))
    (hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0) :
    (Between (Gm.map ((↑) : 𝓞 E → E))).Finite ∧
    (Between (Gm.map ((↑) : 𝓞 E → E))).ncard ≤ (Algebra.norm ℤ Gm.det).natAbs ^ n := by
  classical
  set G := Gm.map ((↑) : 𝓞 E → E) with hG
  set Rg := LinearMap.range (Matrix.mulVecLin Gm) with hRg
  have hcard := card_quot Gm (det_map_ne Gm hdet)
  have hpos : (Algebra.norm ℤ Gm.det).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 (det_map_ne Gm hdet)
  have : Finite ((Fin n → 𝓞 E) ⧸ Rg) := Nat.finite_of_card_ne_zero (hcard ▸ hpos)
  let θ : Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) → Submodule (𝓞 E) (Fin n → E) :=
    fun H ↦ (H.comap Rg.mkQ).map (psi G)
  let Gen : Set (Submodule (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg)) :=
    {H | ∃ s : Fin n → (Fin n → 𝓞 E) ⧸ Rg, Submodule.span (𝓞 E) (Set.range s) = H}
  have hsub : Between G ⊆ θ '' Gen := by
    rintro C ⟨h0, h1, hfg⟩
    have hRC : Rg ≤ C.comap (psi G) := by
      rintro _ ⟨m, rfl⟩
      show psi G (Gm *ᵥ m) ∈ C
      rw [psi_mulVec Gm hdet]
      exact h0 ⟨m, rfl⟩
    refine ⟨(C.comap (psi G)).map Rg.mkQ, ?_, ?_⟩
    · obtain ⟨b, hb, hgen⟩ := Fr.genMod_fg (E := E) (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) Nat.card_pos.ne' n C hfg
      have hb' : ∀ a, ∃ m, psi G m = b a := fun a ↦ h1 (hb a)
      choose mb hmb using hb'
      refine ⟨fun a ↦ Rg.mkQ (mb a), le_antisymm ?_ ?_⟩
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        refine Submodule.mem_map_of_mem ?_
        show psi G (mb a) ∈ C
        rw [hmb]
        exact hb a
      · rintro _ ⟨m, hm, rfl⟩
        obtain ⟨c, z, hz, hx⟩ := hgen (psi G m) hm
        obtain ⟨mz, hmz⟩ := h1 hz
        have hN : (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • Rg.mkQ mz = 0 := card_nsmul_eq_zero'
        have hm_eq : m = ∑ a, c a • mb a + (Nat.card ((Fin n → 𝓞 E) ⧸ Rg)) • mz := by
          apply psi_injective G hdet
          rw [map_add, map_sum, map_nsmul, hx, hmz, ← Nat.cast_smul_eq_nsmul E]
          congr 1
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [map_smul, hmb]
        rw [hm_eq, map_add, map_sum, map_nsmul, hN, add_zero]
        exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
    · show (((C.comap (psi G)).map Rg.mkQ).comap Rg.mkQ).map (psi G) = C
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 hRC, Submodule.map_comap_eq, inf_eq_right.2 h1]
  have hGfin : Gen.Finite := by
    refine (Set.finite_range fun s : Fin n → (Fin n → 𝓞 E) ⧸ Rg ↦ Submodule.span (𝓞 E) (Set.range s)).subset ?_
    rintro H ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hGcard : Gen.ncard ≤ Nat.card ((Fin n → 𝓞 E) ⧸ Rg) ^ n := by
    have := Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound (𝓞 E) ((Fin n → 𝓞 E) ⧸ Rg) n
    rw [← Nat.card_coe_set_eq]
    exact this
  refine ⟨(hGfin.image θ).subset hsub, ?_⟩
  calc (Between G).ncard ≤ (θ '' Gen).ncard := Set.ncard_le_ncard hsub (hGfin.image θ)
    _ ≤ Gen.ncard := Set.ncard_image_le hGfin
    _ ≤ _ := by rw [← hcard]; exact hGcard

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
end

