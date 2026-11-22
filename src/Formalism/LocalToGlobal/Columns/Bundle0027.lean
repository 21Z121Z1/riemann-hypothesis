import Formalism.LocalToGlobal.Columns.Bundle0024
import Formalism.LocalToGlobal.Columns.Bundle0025
import Mathlib
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB
import Formalism.GL3MeanSquares.HookFormulaTorsion.ColumnParametrizationOffDiagonal
import Formalism.LocalToGlobal.Columns.Bundle0023
import Formalism.LocalToGlobal.Columns.Bundle0026
import Formalism.LocalToGlobal.Columns.Bundle0017

-- bundled from Formalism.LocalToGlobal.Columns.ExistsPlaceOverFirstPrime
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Repack0

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {sp : Spaces R F E} {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
  {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {bad : Set (HeightOneSpectrum (𝓞 F))}

def LevPack.toCol (P : LevPack sp.cm R.k sp.gram0 gp A.T R.f bad (C.stab 0) fun c => sp.crdLat0 (clsLat 0 c))
    (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (spl_sig : ∀ i v h x, spl i v h (sigR sp.cm.sig (v.adicCompletion F) x) = swapR _ (spl i v h x))
    (hiw : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), x ∈ P.lev.Uloc v ↔
        (1 : GL (Fin R.k) (v.adicCompletion F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU F R.k v)
    (w1 : HeightOneSpectrum (𝓞 F)) (reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal) :
    ColLevel R F E sp gp C A clsLat where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := P.lev.Lb_int
  Lb_dual := P.lev.Lb_dual
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_le := P.lev.Uloc_le
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  splitG := spl
  splitG_sig := spl_sig
  frG := fun _ _ _ => 1
  Uloc_g := hiw
  fM := P.lev.fM
  fT := P.lev.fT
  fT_ne := P.lev.fT_ne
  fT_T := P.lev.fT_T
  fM_card := P.lev.fM_card
  fT_L := P.lev.fT_L
  UlocAlt := P.lev.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq
  U_compact := P.lev.U_compact
  U_open := P.lev.U_open
  w1 := w1
  reflection_mem_Glev_castSucc := reflection_mem_Glev_castSucc
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := P.cls.stabI_range
  stabI_lat := P.cls.stabI_lat

end Repack0

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
      X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F)

def IwLoc : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
    ∀ x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (v.adicCompletion X.F), x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
      (1 : GL (Fin n) (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F n v

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_iw (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (hI : IwLoc hc u Λ spl) (H : HCrd Pr n fun c => (s c).1.L) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
      ∀ x ∈ UPts hc.sig H.J (v.adicCompletion X.F), x ∈ (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc v ↔
        (1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F H.n' v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact hI

def th_resMap (P : Pl X.E) : 𝓞 X.F ⧸ (underPl X.F P).asIdeal →+* 𝓞 X.E ⧸ P.asIdeal :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E)) (le_of_eq rfl)

include hPr in
theorem th_resMap_bij (P : {P // P ∈ Pr.vT u}) : Function.Bijective (th_resMap (X := X) P.1) := by
  constructor
  · exact Ideal.quotientMap_injective' (le_of_eq rfl)
  · intro b
    haveI : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    haveI : Nontrivial (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.1.isPrime.ne_top
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := hPr.vT_norm u P.1 P.2
    obtain ⟨k, hk⟩ := mem_zmultiples_of_prime_card hcard (g := (1 : 𝓞 X.E ⧸ P.1.asIdeal)) (g' := b) one_ne_zero
    refine ⟨(k : 𝓞 X.F ⧸ (underPl X.F P.1).asIdeal), ?_⟩
    rw [map_intCast, ← hk]
    simp

def tieFv (P : {P // P ∈ Pr.vT u}) : (𝓞 X.E ⧸ P.1.asIdeal) ≃+* (𝓞 X.F ⧸ (tieEV hc hX hPr u P).1.asIdeal) :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm

theorem tieFv_mk (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    tieFv hc hX hPr u P (Ideal.Quotient.mk P.1.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) x)) = Ideal.Quotient.mk _ x :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm_apply_apply (Ideal.Quotient.mk _ x)

include hX hPr in

theorem exists_place_over_first_prime : ∃ v : HeightOneSpectrum (𝓞 X.F), (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal := by
  have hcard : 0 < (Pr.vG 0).card := by rw [hPr.vG_card 0]; exact hX.f_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.1 hcard
  refine ⟨underPl X.F P, ?_⟩
  show (Pr.g 0 : 𝓞 X.F) ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast, ← hPr.piG_norm 0]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs hP)

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MaxSlopeSummandOfFock
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

def TwistDeg (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    0 < n → (∀ τ, Submodule.IsLattice K (M τ)) →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ (I : Submodule (𝓞 K) K) = twId lam M ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)) =
        ∑ τ, ((lam τ).detShift : ℝ) * ((n : ℝ) * (latK K (M τ)).mu)

def ShortBasis (E : Type) [Field E] [NumberField E] (n : ℕ) (Y : Submodule (𝓞 E) (Fin n → E)) (c : ℝ) : Prop :=
  ∃ y : Fin n → Fin n → E, (∀ i, y i ∈ Y) ∧ LinearIndependent E y ∧
    ∀ i, (∑ w : InfinitePlace E, ∑ a, (w (y i a)) ^ 2) / (nPl E : ℝ) ≤ c

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [IsTotallyComplex E] [IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
    rfl
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def ShortC (u : Pr.Word) : Prop :=
  ∀ d : (colGSD W Ch u 0).D, ShortBasis X.E (R.N 0) (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh ((R.k : ℝ) ^ 2 * (2 * vC X) ^ 2)

theorem log_four_pow_identity (k v : ℝ) (hk : 0 < k) (hv : 0 < v) : Real.log k + Real.log (k ^ 3 * (2 * v) ^ 2) = Real.log (4 * k ^ 4 * v ^ 2) := by
  rw [← Real.log_mul hk.ne' (by positivity)]
  congr 1
  ring

theorem max_slope_summand_of_fock (hX : X.Ok) (hPr : Pr.Ok) (hv : 0 < vC X) (hS : FockSubNorm) (hC : HwNormBound) (hTw : TwistDeg X.K) (u : Pr.Word)
    (hT : ShortC W Ch u) : MaxSlopeSummandExplicitForm W Ch u := by
  intro d
  have := hX.cplxK
  have := hX.cplxE
  rw [colValH_eq_tenH]
  obtain ⟨y, hyL, hyli, hyb⟩ := hT d
  have hn0 : 0 < R.N 0 := R.N_pos 0
  have hdet : IsUnit (Matrix.of y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of y)).1 hyli)
  have hdetτ : ∀ τ : X.Tau, IsUnit ((Matrix.of y).map (X.emb τ)).det := fun τ => by
    have : ((Matrix.of y).map (X.emb τ)).det = X.emb τ (Matrix.of y).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact hdet.map _
  set g : X.Tau → GL (Fin (R.N 0)) X.K := fun τ => Matrix.nonsingInvUnit _ (hdetτ τ) with hgdef
  have hgc : ∀ τ c a, (g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) c a = X.emb τ (y c a) := fun τ c a => rfl
  have hg : ∀ τ, ∀ x ∈ EEC W Ch u d τ, ∀ c, ((g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) *ᵥ x) c ∈ (1 : Submodule (𝓞 X.K) X.K) := by
    intro τ x hx c
    have h1 := hx (fun a => X.emb τ (y c a)) (Submodule.subset_span ⟨y c, hyL c, rfl⟩)
    have e : ((g τ : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.K) *ᵥ x) c = x ⬝ᵥ fun a => X.emb τ (y c a) := by
      simp only [Matrix.mulVec, dotProduct, hgc]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [e]
    exact h1

  set hh : InfinitePlace X.E → Fin (R.N 0) → ℝ := fun w c => ∑ a, (w (y c a)) ^ 2 with hhdef
  have hhpos : ∀ w c, 0 < hh w c := by
    intro w c
    obtain ⟨a, ha⟩ := Function.ne_iff.1 (hyli.ne_zero c)
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, ?_⟩
    have : 0 < w (y c a) := (InfinitePlace.pos_iff).2 ha
    positivity
  have hgN : ∀ v τ, gN X.K g v τ = ∑ c, hh (v.comap (X.emb τ)) c := by
    intro v τ
    unfold gN hsN
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.map_apply, Matrix.transpose_apply, hgc, InfinitePlace.comap_apply, ← InfinitePlace.norm_embedding_eq]
  have hpos : ∀ v τ, 0 < gN X.K g v τ := by
    intro v τ
    rw [hgN]
    exact Finset.sum_pos' (fun c _ => (hhpos _ c).le) ⟨⟨0, hn0⟩, Finset.mem_univ _, hhpos _ _⟩
  have hk : (R.N 0 : ℝ) = (R.k : ℝ) := by rw [brz_N_zero]
  have hk1 : (1 : ℝ) ≤ (R.k : ℝ) := by rw [← kap_cast]; have := (Nat.cast_nonneg (kap R) : (0 : ℝ) ≤ _); linarith
  have hmean : ∀ τ, (1 / (nPl X.K : ℝ)) * ∑ v, Real.log (gN X.K g v τ) ≤ Real.log ((R.k : ℝ) ^ 3 * (2 * vC X) ^ 2) := by
    intro τ
    simp only [hgN]
    rw [mean_over_places_comap X.E X.K (X.emb τ) fun w => Real.log (∑ c, hh w c)]
    let e : InfinitePlace X.E ≃ Fin (nPl X.E) := Fintype.equivFin _
    have hz := Formalism.HermitianLattices.ExplicitEstimates.mean_log_explicit (nPl X.E) (R.N 0) (fun i c => hh (e.symm i) c) (vC X)
      (Fintype.card_pos) hn0 hv (fun i c => hhpos _ c) (fun c => by
        rw [Equiv.sum_comp e.symm (fun w => hh w c), hk]
        exact hyb c)
    rw [Equiv.sum_comp e.symm (fun w => Real.log (∑ c, hh w c)), hk] at hz
    exact hz
  obtain ⟨I, hI0, hI, hN⟩ := hTw X.Tau (R.N 0) (W.lamTrue u 0) (EEC W Ch u d) hn0 (EEC_isLattice W Ch u d)
  have hmain := max_slope_twisted_general X.K hS hC (kap_succ R) (W.lamTrue u 0) (EEC W Ch u d) (EEC_isLattice W Ch u d) g hg hpos I hI0 hI
  have hee := eeSlope W Ch hX hPr u d
  rw [sub_eq_add_neg, hN, ← Finset.sum_add_distrib] at hmain
  refine hmain.trans (Finset.sum_le_sum fun τ _ => ?_)
  have hwp : (0 : ℝ) ≤ (wt (plus (lamZ W u τ)) : ℝ) := by
    unfold wt
    exact_mod_cast Finset.sum_nonneg fun i _ => brz_plus_nonneg _ (lamZ_anti W u τ) i
  have e1 : Real.log ((kap R : ℝ) + 1) + (1 / (nPl X.K : ℝ)) * ∑ v, Real.log (gN X.K g v τ) ≤
      Real.log (4 * (R.k : ℝ) ^ 4 * vC X ^ 2) := by
    rw [← log_four_pow_identity (R.k : ℝ) (vC X) (by linarith) hv, kap_cast]
    linarith [hmean τ]
  have e2 := mul_le_mul_of_nonneg_left e1 hwp
  have e3 : ((W.lamTrue u 0 τ).detShift : ℝ) * ((R.N 0 : ℝ) * (latK X.K (EEC W Ch u d τ)).mu) =
      -((lamZ W u τ (Fin.last (kap R)) : ℝ) * logTC Pr u) := by
    rw [hee τ, det_shift_eq_last_weight (kap_succ R), hk]
    show ((lamZ W u τ (Fin.last (kap R)) : ℤ) : ℝ) * _ = _
    field_simp
  rw [e3]
  have e4 : ((kap R : ℝ) + 1) * (kap R : ℝ) / 2 = (R.k : ℝ) * ((R.k : ℝ) - 1) / 2 := by rw [← kap_cast]; ring
  have e5 : (plus (castW (kap_succ R) (W.lamTrue u 0 τ)) 0 : ℝ) + (kap R : ℝ) + 1 = (plus (lamZ W u τ) 0 : ℝ) + (R.k : ℝ) := by
    rw [← kap_cast]
    show (plus (lamZ W u τ) 0 : ℝ) + (kap R : ℝ) + 1 = _
    ring
  rw [e4, e5]
  have e6 : (wt (plus (castW (kap_succ R) (W.lamTrue u 0 τ))) : ℝ) = (wt (plus (lamZ W u τ)) : ℝ) := rfl
  rw [e6]
  linarith

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlRec
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (aOf skipOf fcOf InJ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {hc : CMData X.F X.E} (hX : X.Ok) (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def glevG (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) a t nb skip fc zl c hc1 hmem hlam

theorem glevG_fr (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool) (c) (hc1) (hmem) (hlam) :
    (glevG hX hPr S Ch σ₀ hCh u Λ c₀ s hS hs Q a t nb skip fc zl c hc1 hmem hlam).fr = fun i v h => glvD n v (c i v h) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

def glevPG (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsPG hc σ₀ Λ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (ST := ∅) (π := 1) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    a t nb skip fc zl (fun _ _ _ => 1) (fun _ _ _ => by rw [Units.val_one, map_one]) hmem hlam

theorem glevPG_fr (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool) (hmem) (hlam) :
    (glevPG hPr S Ch σ₀ hCh Λ s hS hs Q a t nb skip fc zl hmem hlam).fr = fun _ _ _ => 1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  funext i v h
  exact glvD_one n v

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

def recGLoc : Formalism.L2.Forms.GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g :=
  tieGLoc d.hPr S d.Ch d.σ₀ hCh

theorem recGLoc_K (hH : HostHyp d) (i : Fin 2) : ((recGLoc a S hCh).piG i : d.host.E) ∈ d.host.K := hH.piG_K i

theorem recGLoc_chi : Formalism.L2.Forms.CharacterCompatible (recGLoc a S hCh) d.R.m := tieGLoc_chiTied d.hPr S d.Ch d.σ₀ hCh

def recUnit (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    (v.adicCompletionIntegers d.X.F)ˣ :=
  if i = d.R.m then S.unitOf d.hPr j v h (d.Pr.piT u) (glk_piT_cong d.hPr u j) else 1

theorem recUnit_res (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers d.X.F) (recUnit S u i j v h) = 1 := by
  unfold recUnit
  split_ifs
  · exact S.unitOf_res d.hPr j v h _ _
  · rw [Units.val_one, map_one]

def recGLev (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Forms.GLev (classAgreement a hS hH hP u i hi).lev (recGLoc a S hCh) (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i)
      (decide (i = d.R.m)) :=
  glevG d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) _ _ _ _ _ _
    (recUnit S u i) (recUnit_res S u i)
    (fun _ _ _ M => by rw [hl]; exact colLevS_mem_iff d.Ch hi _ _ M)
    (fun _ _ _ M hM => by revert hM; rw [hl]; intro hM; exact colLevS_lam_eq d.Ch hi _ _ d.σ₀ M hM)

theorem recGLev_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    (recGLev a S hCh hl hS hH hP u i hi).fr = fun j v h => glvD (d.R.N i) v (recUnit S u i j v h) :=
  glevG_fr d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem recGLev_fr_const (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u u' : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (him : i < d.R.m) : (recGLev a S hCh hl hS hH hP u i hi).fr = (recGLev a S hCh hl hS hH hP u' i hi).fr := by
  rw [recGLev_fr, recGLev_fr]
  funext j v h
  unfold recUnit
  rw [if_neg him.ne, if_neg him.ne]

def recGLevP (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    Formalism.L2.Forms.GLev (parabolicClassAgreement a hS hH hP u).lev (recGLoc a S hCh) d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false :=
  glevPG d.hPr S d.Ch d.σ₀ hCh d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH) _ _ _ _ _ _
    (fun _ _ _ M => by rw [hlP]; exact rowTyG_sharp_mem_iff d.Ch _ _ M)
    (fun _ _ _ M hM => by
      revert hM; rw [hlP]; intro hM
      have e : ((rowTyG d.Ch (rPsharp d.Ch)).inv.inv _).lam ⟨M, hM⟩ = (rowTyG d.Ch (rPsharp d.Ch) _).lam ⟨M, hM⟩ := by
        show (((rowTyG d.Ch (rPsharp d.Ch) _).lam)⁻¹)⁻¹ ⟨M, hM⟩ = _
        rw [inv_inv]
      rw [e]
      exact rowTyG_sharp_lam_eq d.Ch _ _ d.σ₀ M hM)

theorem recGLevP_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    (recGLevP a S hCh hlP hS hH hP u).fr = fun _ _ _ => 1 :=
  glevPG_fr d.hPr S d.Ch d.σ₀ hCh d.levP.inv _ _ _ _ _ _ _ _ _ _ _ _

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedPtSurj
section
noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ptSurj_holds (d : ColDat) : PtSurj d := fun u i =>
  colDecoPtSurj d.sp.cm d.hPr u (d.R.N i) (unimodGenus_holds d.sp.cm (d.R.N i))

theorem points_surjective (d : ColDat) : PtSurjP d := by
  classical
  refine decoPtSurj_of d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs (unimodGenus_holds d.sp.cm _) reduction_surjective_bis ?_ (Finset.disjoint_empty_left _)
  intro PP hP PP' hP'
  exact isSplitSet_of_ok d.hPr d.u₀ PP (Finset.mem_union_right _ (by simpa using hP)) PP' (Finset.mem_union_right _ (by simpa using hP'))

end Formalism.L2.Col
end
end

