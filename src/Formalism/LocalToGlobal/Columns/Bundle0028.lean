import Formalism.LocalToGlobal.Columns.Bundle0026
import Formalism.LocalToGlobal.Columns.Bundle0025
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

-- bundled from Formalism.LocalToGlobal.Columns.TiedValBw
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

def Val.Bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) : Prop :=
  ∀ w, Pl.resChar w = Pr.T u → seenC Pr u (pw w) →
    ∀ (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun),
      x ∈ Submodule.span (intW Pl w) (stepBv W Λ u i v : Set (stepGSD W Λ u i).EqFun) ↔
    ∀ (c : StCl W Λ u i) (B B' : GL (Fin (R.N i)) X.E),
      IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) : Set _) B →
      IsLocBasis (Pr.T u) ((Q.lat c ⊔ Pv v • dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set _) B' →
      ∃ P ∈ IntSpanG σ₀ Pl w (W.lamN u i), ∀ z, (stepEv W Λ σ₀ hσ u i).emb x c z =
        fnOf _ (shiftOf Q.lt)
          (fun τ => @ite _ (τ = tauOfR hX hPr u (pw w) v) (Classical.propDecidable _)
            (atInf Q.emb (B'⁻¹ : GL (Fin (R.N i)) X.E).1 τ) (atInf Q.emb (B⁻¹ : GL (Fin (R.N i)) X.E).1 τ)) P
          (valEY W Λ σ₀ u i Q z)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m)

theorem bwTie_of (Wv : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV i hi (classAgreement a hS hH hP u i hi))
    (hY : Wv.eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi))
    (hBw : Val.Bw (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i d.what₂.places d.plEq (valCrd a hS hH u i hi)
      (atTTied a hH u).Pv) :
    CF.BwTie (atTTied a hH u) Wv := by
  intro w hw hs v x
  rw [hY]
  exact hBw w hw (@of_decide_eq_true _ (Classical.propDecidable _) hs) v x

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValLat
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

omit hc hX σ₀ hσ in
theorem vl_natW_lamTrue (τ : X.Tau) : (W.lamTrue u i τ).natW = (W.lamN u i τ).natW := by
  rw [lamTrue_eq_shW]
  exact natW_shW _ _

include hX in

theorem Val.lat (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K)) (hpw : Function.Surjective pw)
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : ValCrd W Λ σ₀ u i) :
    Val.Lat W Λ hc σ₀ hσ u i Pl Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro x
  rw [(stepGSD W Λ u i).mem_intDel_iff (stepOk W Λ hX u i) (stepGSD W Λ u i).outSec x]
  have key := fun c : StCl W Λ u i => vl_mem_delAtr_iff Pl pw hval X.emb σ₀ hpw (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
    (W.lamTrue u i) (W.lamN u i) (vl_natW_lamTrue W u i) ((stepGSD W Λ u i).outSec.rep c).1.Lsh
    ((stepGSD W Λ u i).outSec.rep c).2.Lsh_lattice ((x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c))
  constructor
  · intro h w c B hB
    have hB' : IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L) B := hB
    rw [rlc_dualSet hc (R.N i)] at hB'
    obtain ⟨P, hP, he⟩ := (key c).1 (h c) w B hB'
    exact ⟨P, hP, fun z => congrFun he z⟩
  · intro h c
    refine (key c).2 fun w B hB => ?_
    have hB' : IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L) B := by
      rw [rlc_dualSet hc (R.N i)]
      exact hB
    obtain ⟨P, hP, he⟩ := h w c B hB'
    exact ⟨P, hP, funext he⟩

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValNorm
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ}

end Poly

section Pair

variable {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

theorem vn_bVV_star (lam : ι → DomWeight n) (s : K →+* ℂ) (i : VVIdx lam) (m : ι × Fin n × Fin n →₀ ℕ) :
    s (star ((bVV K lam i).1.coeff m)) = star (s ((bVV K lam i).1.coeff m)) := by
  rw [bVV_coe]
  obtain ⟨P, hP⟩ := bVVfun_int K lam i
  rw [hP, MvPolynomial.coeff_map]
  simp

theorem vn_pairS (emb : ι → E →+* K) (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (o : Frames (gramC J (embAt s emb))) (ho : ∀ τ, (o.1 τ)ᴴ * gramC J (embAt s emb) τ * o.1 τ = 1) (F F' : VV K lam) :
    ∑ i, ∑ j, starRingEnd ℂ (s ((bVV K lam).repr F i)) * s (pairVr emb lam J (bVV K lam i) (bVV K lam j)) *
        s ((bVV K lam).repr F' j) =
      ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) : ℝ) : ℂ) *
        nfAll lam (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F'.1)) (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1)) := by
  have hexp : ∀ G : VV K lam, Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s G.1) =
      ∑ i, s ((bVV K lam).repr G i) • Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s (bVV K lam i).1) := by
    intro G
    conv_lhs => rw [← (bVV K lam).sum_repr G]
    rw [Submodule.coe_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_mul, MvPolynomial.smul_eq_C_mul]
    congr 1
    exact (Formalism.GradedWeylDivisibility.blockAct ℂ o.1).commutes _
  rw [← nfL_apply, hexp F, hexp F']
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, nfL_apply, Finset.mul_sum,
    RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [pairVr_nfAll emb J lam s o ho (bVV K lam i) (bVV K lam j) (vn_bVV_star lam s i)]
  ring

end Pair

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (lam : X.Tau → DomWeight n) (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

theorem vn_inv_natCast_re (m : ℕ) : (((m : ℕ) : ℂ)⁻¹).re = ((m : ℕ) : ℝ)⁻¹ := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

theorem vn_inv_natCast_mul_re (m : ℕ) (z : ℂ) : (((m : ℕ) : ℂ)⁻¹ * z).re = (((m : ℕ) : ℂ)⁻¹).re * z.re := by
  rw [vn_inv_natCast_re, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem vn_pairAt_re (s : X.K →+* ℂ) (o : Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb)))
    (ho : ∀ τ, (o.1 τ)ᴴ * gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb) τ * o.1 τ = 1) (F : VV X.K lam) :
    ((formGSD (roundPk X lam L) Λ).pairAt (InfinitePlace.mk s) F F).re =
      (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ)) *
        (nfAll lam (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1)) (Formalism.GradedWeylDivisibility.blockAct ℂ o.1 (MvPolynomial.map s F.1))).re := by
  have key := vn_pairS X.emb 1 lam s o ho F F
  rw [← Complex.re_ofReal_mul, ← key]
  rcases InfinitePlace.embedding_mk_eq s with h | h
  · unfold GSD.pairAt
    rw [h]
    rfl
  · rw [← Complex.conj_re]
    congr 1
    unfold GSD.pairAt
    rw [h]
    simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rfl

set_option maxHeartbeats 1000000 in

theorem vn_norm_round (h : (formGSD (roundPk X lam L) Λ).Ok) (R : (formGSD (roundPk X lam L) Λ).Rat) (s : X.K →+* ℂ)
    (o : Frames (gramC (1 : Matrix (Fin n) (Fin n) X.E) (embAt s X.emb))) (ho : o.IsON)
    (φ : (formGSD (roundPk X lam L) Λ).EqFun) :
    (majAt ((formGSD (roundPk X lam L) Λ).hB h) (stdFrame ((formGSD (roundPk X lam L) Λ).hGram h)) (InfinitePlace.mk s) φ φ).re =
      (letI := h.fintypeCl
       ∑ c : (formGSD (roundPk X lam L) Λ).Cl,
        (((Nat.card (MulAction.stabilizer (formGSD (roundPk X lam L) Λ).G ((formGSD (roundPk X lam L) Λ).outSec.rep c)) : ℕ) : ℂ)⁻¹).re *
          (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ)) *
          (nfAll lam
            (subP o.1 (MvPolynomial.map s
              (φ.1 ((formGSD (roundPk X lam L) Λ).outSec.rep c) : VV X.K lam).1))
            (subP o.1 (MvPolynomial.map s
              (φ.1 ((formGSD (roundPk X lam L) Λ).outSec.rep c) : VV X.K lam).1))).re) := by
  let _ := h.fintypeCl
  rw [R.maj_eq h]
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hw : ((((formGSD (roundPk X lam L) Λ).toCSD h).wt c : ℕ) : ℂ) =
      ((Nat.card (MulAction.stabilizer (formGSD (roundPk X lam L) Λ).G ((formGSD (roundPk X lam L) Λ).outSec.rep c)) : ℕ) : ℂ) := by
    congr 1
    exact (@Nat.card_eq_fintype_card _ (h.fintypeStab ((formGSD (roundPk X lam L) Λ).outSec.rep c))).symm
  rw [hw, vn_inv_natCast_mul_re, mul_assoc]
  congr 1
  exact vn_pairAt_re lam L Λ s o (frame_std _ o ho) _

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)

def Val.Norm (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (s : X.K →+* ℂ) (x : (stepGSD W Λ u i).EqFun)
    (Pc : StCl W Λ u i → MvPolynomial (X.Tau × Fin (R.N i) × Fin (R.N i)) X.K),
    (∀ c z, (stepEv W Λ σ₀ hσ u i).emb x c z =
      fnOf _ (shiftOf Q.lt) 1 (MvPolynomial.map σ₀ (Pc c)) (valEY W Λ σ₀ u i Q z)) →
    ∀ o : Frames (gramC Q.J (embAt s X.emb)), o.IsON →
      (majAt (stepH (W := W) (Λ := Λ) hX u i).b (stepH (W := W) (Λ := Λ) hX u i).X (InfinitePlace.mk s) x x).re =
        (letI := (stepOk W Λ hX u i).fintypeCl
         ∑ c : StCl W Λ u i, (((Nat.card (StStab W Λ u i c) : ℕ) : ℂ)⁻¹).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf Q.lt τ)) *
          (nfAll (W.lamN u i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re)

set_option maxHeartbeats 1000000 in
theorem Val.norm (Q : ValCrd W Λ σ₀ u i) : Val.Norm W Λ hX σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro s x Pc hPc o ho
  have hval : ∀ c, (x.1 ((stepGSD W Λ u i).outSec.rep c) : VV X.K (W.lamTrue u i)).1 = Pc c := by
    intro c
    apply evFr_injective (gramC (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) (embAt σ₀ X.emb)) (shiftOf (W.lamTrue u i)) σ₀
      (stdFrC _)
    funext z
    rw [evFr_eq_fnOf, evFr_eq_fnOf]
    exact hPc c z
  have h := vn_norm_round (W.lamTrue u i) (fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i) (stepOk W Λ hX u i)
    (stepRat W Λ hX u i) s o ho x
  refine h.trans ?_
  let _ := (stepOk W Λ hX u i).fintypeCl
  refine Finset.sum_congr rfl fun c _ => ?_
  have hv : (x.1 ((formGSD (roundPk X (W.lamTrue u i) fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i)).outSec.rep c) :
      VV X.K (W.lamTrue u i)).1 = Pc c := hval c
  have h2 : ∀ p q, nfAll (W.lamTrue u i) p q = nfAll (W.lamN u i) p q := by
    intro p q
    rw [lamTrue_eq_shW]
    exact nfAll_shW _ _ _ _
  rw [hv, h2]
  rfl

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ)
  (hi : i ≤ d.R.m) (eV : ((d.colRec a).mem u).A.vT ≃ CF.PlT (d.colRec a) u)

set_option maxHeartbeats 1000000 in

theorem normTie (V : CF.ValTied (D := d.colRec a) u eV i hi (classAgreement a hS hH hP u i hi))
    (hV : V.eY = valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi)) : CF.NormTie V := by
  intro s x Pc hPc o ho
  rw [hV] at hPc
  exact Val.norm (Pr := d.Pr) d.W d.lev d.hX d.σ₀ d.star_cx u i (valCrd a hS hH u i hi) s x Pc hPc o ho

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValRat
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct Pointwise

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

theorem ev_injective : Function.Injective E.ev := by
  intro x y h
  rw [E.ev_eq_lin x, E.ev_eq_lin y] at h
  have h1 := (LinearMap.ker_eq_bot.1 E.lin_ker) h
  apply S.bV.repr.injective
  ext i
  exact σ.injective (congrFun h1 i)

theorem tr_of_mem_Fi {φ : S.Cl → E.Y → ℂ} (hφ : φ ∈ E.Fi) (c : S.Cl) (g : S.G) (hg : g • S.outSec.rep c = S.outSec.rep c) :
    E.tr g (φ c) = φ c := by
  unfold GSD.Ev.Fi at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    rw [E.emb_apply, E.tr_ev, ← ψ.2 g, hg]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [Pi.add_apply, map_add, hx, hy]
  | smul a x _ hx => rw [Pi.smul_apply, map_smul, hx]

theorem exists_emb_iff (h : S.Ok) (φ : S.Cl → E.Y → ℂ) :
    (∃ x, E.emb x = φ) ↔ φ ∈ E.Fi ∧ ∀ c, ∃ v : S.V, φ c = E.ev v := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, rfl⟩, fun c => ⟨_, E.emb_apply x c⟩⟩
  · rintro ⟨hφ, hv⟩
    choose v hv using hv
    have hinv : v ∈ (S.toCSDOf h S.outSec).Forms := by
      intro c γ
      apply E.ev_injective
      show E.ev (S.ρ (γ : S.G) (v c)) = E.ev (v c)
      rw [← E.tr_ev, ← hv c]
      exact E.tr_of_mem_Fi hφ c γ γ.2
    refine ⟨(S.resOf h S.outSec).symm ⟨v, hinv⟩, ?_⟩
    funext c
    rw [E.emb_apply, hv c]
    congr 1
    exact congrFun (congrArg Subtype.val ((S.resOf h S.outSec).apply_symm_apply ⟨v, hinv⟩)) c

end GSD.Ev

section Pol

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

theorem smul_mem_RatSpanG (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : s r • p ∈ RatSpanG s lam := by
  unfold RatSpanG at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatSpanG_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatSpanG s (fun τ => shW (lam τ) (c τ)) = RatSpanG s lam := by
  unfold RatSpanG
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatSpanG (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatSpanG at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatSpanG (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatSpanG s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatSpanG s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatSpanG s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatSpanG s lam c hx

theorem mem_RatSpanG_iff (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    p ∈ RatSpanG s lam ↔ ∃ F ∈ VV K lam, MvPolynomial.map s F = p :=
  ⟨exists_VV_of_mem_RatSpanG s lam, by rintro ⟨F, hF, rfl⟩; exact map_mem_RatSpanG s lam hF⟩

end Pol

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem roundEv_exists_emb_iff (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (lam : X.Tau → DomWeight n) (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)
    (h : (formGSD (roundPk X lam L) Λ).Ok) (φ : (formGSD (roundPk X lam L) Λ).Cl → FrS X σ₀ n → ℂ) :
    (∃ x, (roundEv σ₀ hσ lam L Λ).emb x = φ) ↔
      φ ∈ (roundEv σ₀ hσ lam L Λ).Fi ∧ ∀ c, ∃ P ∈ RatSpanG σ₀ lam, φ c = fnOf _ (shiftOf lam) 1 P := by
  rw [(roundEv σ₀ hσ lam L Λ).exists_emb_iff h φ]
  refine and_congr_right fun _ => forall_congr' fun c => ?_
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, map_mem_RatSpanG σ₀ lam (v : VV X.K lam).2, hv⟩
  · rintro ⟨P, hP, hv⟩
    obtain ⟨F, hF, rfl⟩ := exists_VV_of_mem_RatSpanG σ₀ lam hP
    exact ⟨(⟨F, hF⟩ : VV X.K lam), hv⟩

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)

include hX in

theorem Val.rat (Q : ValCrd W Λ σ₀ u i) : Val.Rat W Λ σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro φ
  have h := roundEv_exists_emb_iff σ₀ hσ (W.lamTrue u i) (fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i)
    (stepOk W Λ hX u i) φ
  have e : RatSpanG σ₀ (W.lamTrue u i) = RatSpanG σ₀ (W.lamN u i) := by
    rw [lamTrue_eq_shW]
    exact RatSpanG_shW σ₀ _ _
  rw [e] at h
  refine h.trans (and_congr_right fun _ => forall_congr' fun c => ?_)
  constructor
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, hP, fun z => congrFun hv z⟩
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, hP, funext hv⟩

end Gen

end Formalism.L2.Col
end
end

