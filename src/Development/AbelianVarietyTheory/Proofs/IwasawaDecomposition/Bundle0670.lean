import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.RootSum

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

theorem mult_tau (t : D.what₂.Tau) : S.Dw.mult (DV.tauEmb D t) = S.Dw.p := by
  simp [Datum.mult, A.cm t]

theorem conj_tau_ne (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0 := by
    have h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := A.cm t
    rw [← h0] at h ⊢
    exact h
  have hd : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
  have h3 : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  simp [pow_two, h3] at h2
  nlinarith [sq_nonneg A.H.rt0.re]

theorem mult_conj_tau (t : D.what₂.Tau) : S.Dw.mult (conjEmb (DV.tauEmb D t)) = S.Dw.q := by
  rw [Datum.mult, if_neg (conj_tau_ne t)]

theorem tau_inj' {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb' (σ : D.host.E →+* ℂ) : conjEmb (conjEmb σ) = σ :=
  RingHom.ext fun a => by simp [conjEmb]

theorem eq_tau_or_conj (σ : D.host.E →+* ℂ) :
    (σ (A.H.rt : D.host.E) = A.H.rt0 ∧ ∃ t, σ = DV.tauEmb D t) ∨
      (σ (A.H.rt : D.host.E) ≠ A.H.rt0 ∧ ∃ t, σ = conjEmb (DV.tauEmb D t)) := by
  have hmem : ∀ ρ : D.host.E →+* ℂ, ρ ∈ cmTypeOfSqrt D ↔ ρ (A.H.rt : D.host.E) = A.H.rt0 := fun ρ => by
    rw [mem_cm_type_iff, A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt]
  by_cases h : σ (A.H.rt : D.host.E) = A.H.rt0
  · exact Or.inl ⟨h, DatOf.exists_tauEmb D ((hmem σ).2 h)⟩
  · refine Or.inr ⟨h, ?_⟩
    have hc : ComplexEmbedding.conjugate σ ∈ cmTypeOfSqrt D := by
      by_contra hc
      exact h ((hmem σ).1 ((cm_type_mem_iff_conj_not_mem D σ).2 hc))
    obtain ⟨t, ht⟩ := DatOf.exists_tauEmb D hc
    refine ⟨t, RingHom.ext fun a => ?_⟩
    have := congrArg (fun ρ : D.host.E →+* ℂ => starRingEnd ℂ (ρ a)) ht
    simp only [ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, RingHomCompTriple.comp_apply,
      Complex.conj_conj] at this
    simpa [conjEmb] using this

def rootLetter (x : DV.Rt D.what₂.Tau N) : Letter S.Dw :=
  if h : (x.2 : ℕ) < S.Dw.p then ⟨DV.tauEmb D x.1, ⟨x.2, by rw [mult_tau]; exact h⟩⟩
  else ⟨conjEmb (DV.tauEmb D x.1), ⟨S.Dw.p + S.Dw.q - 1 - x.2, by
    rw [mult_conj_tau]; have := S.rank_eq; have := x.2.2; omega⟩⟩

open Classical in

theorem rootExp_eq (x : DV.Rt D.what₂.Tau N) (l : Letter S.Dw) :
    rootExp S x l = if l = rootLetter S x then (if (x.2 : ℕ) < S.Dw.p then 1 else -1) else 0 := by
  classical
  simp only [rootExp, rootEx, rootSym]
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · have hm : (x.2 : ℕ) < S.Dw.mult (DV.tauEmb D x.1) := by rw [mult_tau]; exact h
    simp only [if_pos h, expo_single, letterOf, dif_pos hm, rootLetter, dif_pos h, Option.some.injEq]
    by_cases e : l = ⟨DV.tauEmb D x.1, ⟨x.2, hm⟩⟩ <;> simp [e, eq_comm]
  · have hm : S.Dw.p + S.Dw.q - 1 - (x.2 : ℕ) < S.Dw.mult (conjEmb (DV.tauEmb D x.1)) := by
      rw [mult_conj_tau]; have := S.rank_eq; have := x.2.2; omega
    simp only [if_neg h, expo_single, letterOf, dif_pos hm, rootLetter, dif_neg h, Option.some.injEq]
    by_cases e : l = ⟨conjEmb (DV.tauEmb D x.1), ⟨_, hm⟩⟩ <;> simp [e, eq_comm]

theorem rootLetter_key (x : DV.Rt D.what₂.Tau N) :
    ((rootLetter S x).1, ((rootLetter S x).2 : ℕ)) =
      if (x.2 : ℕ) < S.Dw.p then (DV.tauEmb D x.1, (x.2 : ℕ))
      else (conjEmb (DV.tauEmb D x.1), S.Dw.p + S.Dw.q - 1 - x.2) := by
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · rw [rootLetter, dif_pos h, if_pos h]
  · rw [rootLetter, dif_neg h, if_neg h]

theorem letter_ext {l l' : Letter S.Dw} (h : (l.1, (l.2 : ℕ)) = (l'.1, (l'.2 : ℕ))) : l = l' := by
  obtain ⟨a, i⟩ := l
  obtain ⟨b, k⟩ := l'
  obtain ⟨rfl, h'⟩ := Prod.mk.inj h
  obtain rfl : i = k := Fin.ext h'
  rfl

theorem rootLetter_bijective : Function.Bijective (rootLetter S) := by
  have hr := S.rank_eq
  have key : ∀ x y, rootLetter S x = rootLetter S y →
      ((rootLetter S x).1, ((rootLetter S x).2 : ℕ)) = ((rootLetter S y).1, ((rootLetter S y).2 : ℕ)) :=
    fun x y h => by rw [h]
  refine ⟨fun x y hxy => ?_, fun l => ?_⟩
  · have e := key x y hxy
    rw [rootLetter_key, rootLetter_key] at e
    have hx := x.2.2
    have hy := y.2.2
    split_ifs at e with h1 h2 h2
    · obtain ⟨e1, e2⟩ := Prod.mk.inj e
      exact Prod.ext (tau_inj' e1) (Fin.ext e2)
    · exact absurd (Prod.mk.inj e).1 (fun h => conj_tau_ne y.1 (h ▸ A.cm x.1))
    · exact absurd (Prod.mk.inj e).1 (fun h => conj_tau_ne x.1 (h.symm ▸ A.cm y.1))
    · obtain ⟨e1, e2⟩ := Prod.mk.inj e
      have e1' : DV.tauEmb D x.1 = DV.tauEmb D y.1 := by
        have := congrArg conjEmb e1
        simpa [conjEmb_conjEmb'] using this
      exact Prod.ext (tau_inj' e1') (Fin.ext (by omega))
  · obtain ⟨σ, i⟩ := l
    rcases eq_tau_or_conj (A := A) σ with ⟨hσ, t, rfl⟩ | ⟨hσ, t, rfl⟩
    · have hi : (i : ℕ) < S.Dw.p := by have := i.isLt; have := mult_tau S t; omega
      refine ⟨(t, ⟨i, by omega⟩), letter_ext S ?_⟩
      rw [rootLetter_key, if_pos hi]
    · have hi : (i : ℕ) < S.Dw.q := by have := i.isLt; have := mult_conj_tau S t; omega
      have hn : ¬ (S.Dw.p + S.Dw.q - 1 - i < S.Dw.p) := by omega
      refine ⟨(t, ⟨S.Dw.p + S.Dw.q - 1 - i, by omega⟩), letter_ext S ?_⟩
      rw [rootLetter_key, if_neg hn]
      exact Prod.ext rfl (by dsimp only; omega)

theorem divOf_root {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp) (x : DV.Rt D.what₂.Tau N) :
    divOf (Φ.C k) (rootExp S x) =
      (if (x.2 : ℕ) < S.Dw.p then 1 else -1 : ℤ) • (Φ.C k).gr (rootLetter S x).1 (rootLetter S x).2 := by
  classical
  rw [divOf]
  simp_rw [rootExp_eq, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

end GlobalTheory.RootSum

namespace GlobalTheory.RootSum

theorem sum_two_roots_ge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), (∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 : ℤ) • divOf (Φ.C k) (rootExp S x)) = -(∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2) + ∑ x : DV.Rt D.what₂.Tau N, divOf (Φ.C k) (rootExp S x) := by
  intro D A N j S κ s Φ k
  rw [← Fintype.sum_bijective (rootLetter S) (rootLetter_bijective S)
    (fun x => (Φ.C k).gr (rootLetter S x).1 (rootLetter S x).2) (fun x : Letter S.Dw => (Φ.C k).gr x.1 x.2)
    (fun _ => rfl)]
  simp_rw [divOf_root, S.p_eq]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · simp
  · simp only [neg_smul, one_smul, smul_neg]
    rw [two_smul]
    abel

end GlobalTheory.RootSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameOfFlagAt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.LocM.Cht.FamPf

theorem hom_ext_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) (W : ValuationSubring ℂ) {R : Type} [CommRing R] (g h : c.F →+* R)
    (e : g.comp (c.V W).subtype = h.comp (c.V W).subtype) : g = h := by
  have e' : ∀ x (hx : x ∈ c.V W), g x = h x := fun x hx => congrArg (fun f => f ⟨x, hx⟩) e
  ext x
  by_cases h0 : x = 0
  · simp [h0]
  rcases (c.V W).mem_or_inv_mem x with h1 | h1
  · exact e' x h1
  · have h2 := e' _ h1
    have hg : g x * g x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    have hh : h x * h x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    calc g x = g x * (h x * h x⁻¹) := by rw [hh, mul_one]
      _ = (g x * g x⁻¹) * h x := by rw [h2]; ring
      _ = h x := by rw [hg, one_mul]

theorem range_of_base {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {X : Scheme.{0}} (x : Sp k ⟶ X) {T : Set X}
    (h : Set.range (spMap φ ≫ x) ⊆ T) : Set.range x ⊆ T := by
  rintro _ ⟨s, rfl⟩
  have e : spMap φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k') = s := (inferInstance : Subsingleton (PrimeSpectrum k)).elim _ _
  rw [← e]
  exact h ⟨_, rfl⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem vec_eq_of_cart {X' X : Scheme.{0}} {t' : SAB H X'} {t : SAB H X} {g : X' ⟶ X} (m : SABMap t' t g) {T : Scheme.{0}}
    {v v' : T ⟶ t'.G.left} (hv : v ≫ t'.G.hom = v' ≫ t'.G.hom) (h : v ≫ m.φ = v' ≫ m.φ) : v = v' :=
  m.cart.1.hom_ext h hv

theorem exists_incl_of_isTrans {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ} (h : IsTrans i i₂ τ mu) :
    ∃ b : i.c.V W →+* i₂.c.V W, IsIncl b ∧ τ ≫ (Y i).s = (Y i₂).s ≫ spMap b := by
  obtain ⟨b, π', r, hb, h1, h2, -⟩ := h
  exact ⟨b, hb, by rw [← h1, ← h2, Category.assoc, Category.assoc, pullback.condition]⟩

theorem emb_agree {i i₂ : Idx H p} (hc : i.c.F ≤ i₂.c.F) {b : i.c.V W →+* i₂.c.V W} (hb : IsIncl b) {R : Type} [CommRing R]
    (g : i.c.F →+* R) (g₂ : i₂.c.F →+* R)
    (e : g.comp (i.c.V W).subtype = (g₂.comp (i₂.c.V W).subtype).comp b) (σ : E →+* ℂ) (a : 𝓞 E) :
    g₂ (embK i₂.c σ a) = g (embK i.c σ a) := by
  have h : g₂.comp (IntermediateField.inclusion hc).toRingHom = g := by
    refine hom_ext_V i.c W _ _ ?_
    rw [e]
    ext x
    exact congrArg g₂ (Subtype.ext (hb x).symm)
  rw [← h]
  exact congrArg g₂ (Subtype.ext rfl)

theorem x0_trans {C : SCF p} {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} (P : PointsOfFlagModel.PtC (Y i) C) (P' : PointsOfFlagModel.PtC (Y i₂) C)
    (h : P'.yt ≫ τ = P.yt) : P'.x0 ≫ τ = P.x0 := by
  have e : ∀ Q : PointsOfFlagModel.PtC (Y i) C, Q.x0 = spMap (intO ↥C.S).subtype ≫ Q.yt := fun Q => Q.ext.symm
  have e' : P'.x0 = spMap (intO ↥C.S).subtype ≫ P'.yt := P'.ext.symm
  rw [e, e', Category.assoc, h]

theorem x0_s {C : SCF p} {i : Idx H p} (P : PointsOfFlagModel.PtC (Y i) C) : P.x0 ≫ (Y i).s = spMap (P.fK.comp (i.c.V W).subtype) := by
  have e : P.x0 = spMap (intO ↥C.S).subtype ≫ P.yt := P.ext.symm
  rw [e, Category.assoc, P.yt_over, ← spMap_comp, P.compat]

theorem fK_agree {C : SCF p} {i i₂ : Idx H p} (hc : i.c.F ≤ i₂.c.F) {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ}
    (ht : IsTrans i i₂ τ mu) (P : PointsOfFlagModel.PtC (Y i) C) (P' : PointsOfFlagModel.PtC (Y i₂) C) (h : P'.yt ≫ τ = P.yt) (σ : E →+* ℂ) (a : 𝓞 E) :
    P'.fK (embK i₂.c σ a) = P.fK (embK i.c σ a) := by
  obtain ⟨b, hb, hs⟩ := exists_incl_of_isTrans ht
  refine emb_agree hc hb _ _ (spMap_inj ?_) σ a
  have e := x0_s (W := W) P
  rw [← x0_trans P P' h, Category.assoc, hs, ← Category.assoc, x0_s, ← spMap_comp] at e
  exact e.symm

theorem frame_of_flagAt {C : SCF p} (Z : Mdl Y i₀) (P : PointsOfFlagModel.PtC (Y Z.i) C) (g : Sp ↥C.S ⟶ Z.X) (hg : g ≫ Z.π = P.x0)
    (u : Vecs Dw (Y Z.i).t ↥C.S) (h : Z.FlagAt g u) : IsFrame (Y Z.i).t P.fK P.x0 u := by
  obtain ⟨a, φ, h1, h2, -⟩ := h
  have e : φ.comp (Z.alg a) = P.fK := by
    refine hom_ext_V _ W _ _ (spMap_inj ?_)
    have e1 : g ≫ Z.s = spMap (P.fK.comp (Z.i.c.V W).subtype) := by
      rw [← Z.π_s, ← Category.assoc, hg, x0_s]
    have e2 : g ≫ Z.s = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
      rw [← h1, Category.assoc, Z.alg_s, ← spMap_comp]
    exact e2.symm.trans e1
  rw [hg, e] at h2
  exact h2

theorem vec_cocycle (hC : CocycleSt) {i₁ i₂ i₃ : Idx H p} {τ : (Y i₂).X ⟶ (Y i₁).X} {mu : SABMap (Y i₂).t (Y i₁).t τ}
    {τ' : (Y i₃).X ⟶ (Y i₂).X} {mu' : SABMap (Y i₃).t (Y i₂).t τ'} {τ'' : (Y i₃).X ⟶ (Y i₁).X}
    {mu'' : SABMap (Y i₃).t (Y i₁).t τ''} (h₁ : i₁.l.Dvd i₂.l) (h₂ : i₂.l.Dvd i₃.l) (t₁ : IsTrans i₁ i₂ τ mu)
    (t₂ : IsTrans i₂ i₃ τ' mu') (t₃ : IsTrans i₁ i₃ τ'' mu'') {T : Scheme.{0}} (v : T ⟶ (Y i₃).t.G.left)
    (e : T ⟶ (Xo i₃.l).XF i₃.c) (hv : v ≫ (Y i₃).t.G.hom = e ≫ (Y i₃).j) : v ≫ mu'.φ ≫ mu.φ = v ≫ mu''.φ := by
  have hp := (Y i₃).m.cart.1
  have := hC E H Dw Xo p W Y i₁ i₂ i₃ τ mu τ' mu' τ'' mu'' h₁ h₂ t₁ t₂ t₃
  rw [← hp.lift_fst v e hv, Category.assoc, Category.assoc, this]

open Classical in

theorem fam_core (hE : ExtendSt) (hM : FrameMoveSt) (hC : CocycleSt) (hN : N2 Y) {C : SCF p}
    (P : ∀ i : Idx H p, PointsOfFlagModel.PtC (Y i) C)
    (hP : ∀ (i i' : Idx H p) (τ : (Y i').X ⟶ (Y i).X) (mu : SABMap (Y i').t (Y i).t τ), i.l.Dvd i'.l → IsTrans i i' τ mu →
      (P i').yt ≫ τ = (P i).yt)
    (Z : Mdl Y i₀) (y : PtAt Z C) (hy : y.P = P Z.i) (u : Vecs Dw (Y Z.i).t ↥C.S) (hu : Z.FlagAt y.gen u) :
    ∃ fam : Fam Y i₀ C, fam.pt Z = y ∧ ∀ (Z' : Mdl Y i₀) (τ : (Y Z.i).X ⟶ (Y Z'.i).X) (mu : SABMap (Y Z.i).t (Y Z'.i).t τ),
      Z'.i.l.Dvd Z.i.l → IsTrans Z'.i Z.i τ mu →
      (fam.pt Z').gen ≫ Z'.π = (P Z'.i).x0 ∧ Z'.FlagAt (fam.pt Z').gen (fun σ i => u σ i ≫ mu.φ) := by
  have tr : ∀ Z' : Mdl Y i₀, ∃ (τ : (Y Z'.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z'.i).t (Y i₀).t τ), IsTrans i₀ Z'.i τ mu :=
    fun Z' => ⟨_, exists_isTrans hN i₀ Z'.i Z'.dvd Z'.le⟩
  choose τ₀ mu₀ h₀ using tr
  have hyg : y.gen ≫ Z.π = (P Z.i).x0 := by
    have e : (P Z.i).x0 = spMap (intO ↥C.S).subtype ≫ (P Z.i).yt := (P Z.i).ext.symm
    rw [e, ← hy, ← y.z_π, PtAt.gen, Category.assoc]
  let u₀ : Vecs Dw (Y i₀).t ↥C.S := fun σ i => u σ i ≫ (mu₀ Z).φ
  have hu₀ : IsFrame (Y i₀).t (P i₀).fK (P i₀).x0 u₀ := by
    have h1 := (hM E H Dw i₀.l Z.i.l i₀.c Z.i.c _ _ (Y i₀).t (Y Z.i).t (τ₀ Z) (mu₀ Z) ↥C.S (P i₀).fK (P Z.i).fK (P Z.i).x0
      (fK_agree Z.le (h₀ Z) _ _ (hP _ _ _ _ Z.dvd (h₀ Z)))).1 u (frame_of_flagAt Z (P Z.i) y.gen hyg u hu)
    rw [x0_trans _ _ (hP _ _ _ _ Z.dvd (h₀ Z))] at h1
    exact h1

  let Good : ∀ Z' : Mdl Y i₀, (Sp ↥C.S ⟶ Z'.X) → Vecs Dw (Y Z'.i).t ↥C.S → Prop := fun Z' g u' =>
    g ≫ Z'.π = (P Z'.i).x0 ∧ Z'.FlagAt g u' ∧ ∀ σ i, u' σ i ≫ (mu₀ Z').φ = u₀ σ i
  have good_y : Good Z y.gen u := ⟨hyg, hu, fun _ _ => rfl⟩
  have ex : ∀ Z' : Mdl Y i₀, ∃ (q : PtAt Z' C) (u' : Vecs Dw (Y Z'.i).t ↥C.S), Good Z' q.gen u' := by
    intro Z'
    have hx := hP _ _ _ _ Z'.dvd (h₀ Z')
    obtain ⟨u', hu', e⟩ := (hM E H Dw i₀.l Z'.i.l i₀.c Z'.i.c _ _ (Y i₀).t (Y Z'.i).t (τ₀ Z') (mu₀ Z') ↥C.S (P i₀).fK
      (P Z'.i).fK (P Z'.i).x0 (fK_agree Z'.le (h₀ Z') _ _ hx)).2 u₀ (by rw [x0_trans _ _ hx]; exact hu₀)
    obtain ⟨w', ⟨hw1, hw2⟩, -⟩ := Z'.bij ↥C.S (P Z'.i).fK (P Z'.i).y (P Z'.i).y_over u' hu'
    have hr : Set.range w' ⊆ Z'.opn := by
      rintro _ ⟨s, rfl⟩
      refine ⟨(P Z'.i).y s, ?_⟩
      exact (congrArg (fun f => f s) hw1).symm
    have hs : w' ≫ Z'.s = spMap ((intO ↥C.S).subtype.comp (P Z'.i).alg) := by
      rw [← Z'.π_s, ← Category.assoc, hw1, (P Z'.i).compat]
      exact x0_s (P Z'.i)
    obtain ⟨q, hq⟩ := (hE E H Dw Xo p W Y i₀).2.2 Z' C w' (P Z'.i).alg hr hs
    exact ⟨q, u', by rw [hq]; exact ⟨hw1, hw2, e⟩⟩
  choose q uq hq using ex

  have key : ∀ (Z₁ Z₂ : Mdl Y i₀) (g₁ : Sp ↥C.S ⟶ Z₁.X) (g₂ : Sp ↥C.S ⟶ Z₂.X) (u₁ : Vecs Dw (Y Z₁.i).t ↥C.S)
      (u₂ : Vecs Dw (Y Z₂.i).t ↥C.S), Good Z₁ g₁ u₁ → Good Z₂ g₂ u₂ → ∀ (τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X)
      (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ), Z₂.i.l.Dvd Z₁.i.l → IsTrans Z₂.i Z₁.i τ mu →
      (fun σ i => u₁ σ i ≫ mu.φ) = u₂ := by
    intro Z₁ Z₂ g₁ g₂ u₁ u₂ G₁ G₂ τ mu hd ht
    funext σ i
    have f₁ := (frame_of_flagAt Z₁ (P Z₁.i) g₁ G₁.1 u₁ G₁.2.1).1 σ i
    have f₂ := (frame_of_flagAt Z₂ (P Z₂.i) g₂ G₂.1 u₂ G₂.2.1).1 σ i
    have hx := hP _ _ _ _ hd ht
    refine vec_eq_of_cart (mu₀ Z₂) ?_ ?_
    · rw [f₂.1.1, Category.assoc, mu.cart.1.w, ← Category.assoc, f₁.1.1, Category.assoc, x0_trans _ _ hx]
    · rw [Category.assoc, G₂.2.2 σ i, ← G₁.2.2 σ i]
      exact vec_cocycle hC Z₂.dvd hd (h₀ Z₂) ht (h₀ Z₁) (u₁ σ i)
        (spMap (algebraMap ↥C.S (DualNumber ↥C.S)) ≫ (P Z₁.i).y) (by rw [f₁.1.1, Category.assoc]; rfl)
  let pt : ∀ Z' : Mdl Y i₀, PtAt Z' C := Function.update q Z y
  have hpt : pt Z = y := Function.update_self _ _ _
  have good : ∀ Z' : Mdl Y i₀, ∃ u' : Vecs Dw (Y Z'.i).t ↥C.S, Good Z' (pt Z').gen u' := by
    intro Z'
    by_cases h : Z' = Z
    · subst h
      exact ⟨u, by rw [hpt]; exact good_y⟩
    · refine ⟨uq Z', ?_⟩
      have : pt Z' = q Z' := Function.update_of_ne h _ _
      rw [this]
      exact hq Z'
  refine ⟨⟨pt, fun Z₁ Z₂ hc => ?_⟩, hpt, fun Z' τ mu hd ht => ?_⟩
  · obtain ⟨u₁, G₁⟩ := good Z₁
    obtain ⟨u₂, G₂⟩ := good Z₂
    obtain ⟨mu, ht⟩ := exists_isTrans hN Z₂.i Z₁.i hc.1 hc.2.1
    have hx := hP _ _ _ _ hc.1 ht
    refine ⟨_, mu, u₁, ht, ?_, G₁.2.1, ?_⟩
    · rw [G₂.1, ← Category.assoc, G₁.1]
      exact (x0_trans _ _ hx).symm
    · rw [key Z₁ Z₂ _ _ u₁ u₂ G₁ G₂ _ mu hc.1 ht]
      exact G₂.2.1
  · obtain ⟨u₂, G₂⟩ := good Z'
    refine ⟨G₂.1, ?_⟩
    rw [key Z Z' _ _ u u₂ good_y G₂ τ mu hd ht]
    exact G₂.2.1

theorem rat_core (hE : ExtendSt) (hF : FlagBaseSt) (hM : FrameMoveSt) {C : SCF p} (K : Subfield ↥C.S)
    (Z Z' : Mdl Y i₀) (hc : Z'.i.c.F ≤ Z.i.c.F) {τ : (Y Z.i).X ⟶ (Y Z'.i).X} {mu : SABMap (Y Z.i).t (Y Z'.i).t τ}
    (ht : IsTrans Z'.i Z.i τ mu) (P : PointsOfFlagModel.PtC (Y Z.i) C) (P' : PointsOfFlagModel.PtC (Y Z'.i) C) (hP : P.yt ≫ τ = P'.yt)
    (w : Sp ↥K ⟶ Z.X) (hw : (spMap K.subtype ≫ w) ≫ Z.π = P.x0) (u₁ : Vecs Dw (Y Z.i).t ↥K) (h₁ : Z.FlagAt w u₁)
    (g : Sp ↥C.S ⟶ Z'.X) (hg : g ≫ Z'.π = P'.x0)
    (hf : Z'.FlagAt g (fun σ i => (u₁.bc K.subtype) σ i ≫ mu.φ)) : ∃ w' : Sp ↥K ⟶ Z'.X, spMap K.subtype ≫ w' = g := by
  obtain ⟨a, φ, e1, e2, -⟩ := h₁
  have hbc : spMap K.subtype ≫ w ≫ Z.π ≫ τ = P'.x0 := by
    rw [← x0_trans P' P hP, ← hw]; simp only [Category.assoc]
  have hr : Set.range (w ≫ Z.π ≫ τ) ⊆ Set.range (Y Z'.i).j := by
    refine range_of_base K.subtype _ ?_
    rw [hbc]
    rintro _ ⟨s, rfl⟩
    exact ⟨P'.y s, rfl⟩
  obtain ⟨f, yK, h1, h2⟩ := (hE E H Dw Xo p W Y i₀).1 Z'.i ↥K (w ≫ Z.π ≫ τ) hr
  obtain ⟨b, hb, hs⟩ := exists_incl_of_isTrans ht
  have hV : f.comp (Z'.i.c.V W).subtype = (((φ.comp (Z.alg a))).comp (Z.i.c.V W).subtype).comp b := by
    refine spMap_inj ?_
    have l1 : (w ≫ Z.π ≫ τ) ≫ (Y Z'.i).s = spMap (f.comp (Z'.i.c.V W).subtype) := by
      rw [← h2, spMap_comp, ← h1, Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (Y Z'.i).jQ,
        (Y Z'.i).jQ_over, Category.assoc]
    have l2 : (w ≫ Z.π ≫ τ) ≫ (Y Z'.i).s = spMap (((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype).comp b) := by
      have e3 : w ≫ Z.s = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
        rw [← e1, Category.assoc, Z.alg_s, ← spMap_comp]
      rw [Category.assoc, Category.assoc, hs, ← Category.assoc Z.π, Z.π_s, ← Category.assoc, e3, ← spMap_comp]
    exact l1.symm.trans l2
  have hfr := (hM E H Dw Z'.i.l Z.i.l Z'.i.c Z.i.c _ _ (Y Z'.i).t (Y Z.i).t τ mu ↥K f (φ.comp (Z.alg a)) (w ≫ Z.π)
    (emb_agree hc hb _ _ hV)).1 u₁ e2
  have hx : (w ≫ Z.π) ≫ τ = yK ≫ (Y Z'.i).j := by rw [h2, Category.assoc]
  rw [hx] at hfr
  obtain ⟨w', ⟨hw1, hw2⟩, -⟩ := Z'.bij ↥K f yK h1 _ hfr
  have hbase := (hF E H Dw Xo p W Y i₀ Z' ↥K w').2 ↥C.S K.subtype _ hw2
  have heq : Vecs.bc K.subtype (fun σ i => u₁ σ i ≫ mu.φ) = fun σ i => (u₁.bc K.subtype) σ i ≫ mu.φ := by
    funext σ i
    simp only [Vecs.bc, Category.assoc]
  rw [heq] at hbase
  have hg' : (spMap K.subtype ≫ w') ≫ Z'.π = P'.x0 := by
    rw [Category.assoc, hw1, h2, hbc]
  have hF' := frame_of_flagAt Z' P' g hg _ hf
  exact ⟨w', (Z'.bij ↥C.S P'.fK P'.y P'.y_over _ hF').unique ⟨hg', hbase⟩ ⟨hg, hf⟩⟩

end Free

end GlobalTheory.LocM.Cht.FamPf

namespace GlobalTheory.LocM.Cht

open GlobalTheory.LocM.Cht.FamPf

end GlobalTheory.LocM.Cht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_power : ∀ (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ), e.IsGen → GlobalTheory.TraitGen.ExtAt L x e →
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  first | exact @GlobalTheory.TraitGen.extAt_lbPow | exact GlobalTheory.TraitGen.extAt_lbPow | (intros; apply GlobalTheory.TraitGen.extAt_lbPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensorStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_tensor : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  first | exact @GlobalTheory.TraitGen.exists_tens_extAt | exact GlobalTheory.TraitGen.exists_tens_extAt | (intros; apply GlobalTheory.TraitGen.exists_tens_extAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericStalkPointInInteriorStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_stalk_point_in_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)), p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  first | exact @GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j | exact GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j | (intros; apply GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.hermForm_im_real_comb (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, (hermForm Hm (x i) (x j)).im = M i j) (u v : Fin r → ℝ) :
    (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  have key : hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)
      = ∑ m, ∑ m', ((u m * v m' : ℝ) : ℂ) * hermForm Hm (x m) (x m') := by
    simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
      dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    push_cast
    ring
  rw [key]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConjStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_smooth_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | exact GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | (intros; apply GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_along_dvr_arcs : ∀ (X : Scheme.{0}) (BD : GlobalTheory.EffCartierData X) (R : Type) [CommRing R] [IsDomain R] (u : R), u ≠ 0 →
    ∀ (x : Sp (FractionRing R) ⟶ X) (n : ℕ),
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ u ^ n}) →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.dual BD.lb).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.dual BD.lb) x e := by
  first | exact @GlobalTheory.TraitGen.exists_dual_gen_extAt | exact GlobalTheory.TraitGen.exists_dual_gen_extAt | (intros; apply GlobalTheory.TraitGen.exists_dual_gen_extAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldTies_of_rayField_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre), X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  first | exact @GlobalTheory.AtMember.fieldTies_of_ksExact | exact GlobalTheory.AtMember.fieldTies_of_ksExact | (intros; apply GlobalTheory.AtMember.fieldTies_of_ksExact <;> assumption)
end

