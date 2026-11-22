import Formalism.LocalToGlobal.Columns.Bundle0029
import Formalism.LocalToGlobal.Columns.Bundle0038
import Formalism.LocalToGlobal.Columns.XtLamGvSCongr

-- bundled from Formalism.LocalToGlobal.Columns.TiedHFv
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

def fvMeW (w : HeightOneSpectrum (𝓞 X.F)) (P : Pr.vT u) (hov : IsOver w P.1) :
    fMod hc n (Pr.vT u) w ≃+ (𝓞 X.E ⧸ P.1.asIdeal) :=
  fvMeL hc n w (basePi_of_ok hX hPr u) P.2 hov ((basePi_of_ok hX hPr u).over_unique hc P.2 hov) _ _ (fv_unit hPr u c₀ P)

theorem fv_tieW (w : HeightOneSpectrum (𝓞 X.F)) (P : Pr.vT u) (hov : IsOver w P.1)
    (y : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (hyU : y ∈ UAd hc n) (d : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hd : decoOfD n (Pr.vT u) Pr.vGs c₀ y = d) (z : Sp X.E n) (hzL : z ∈ d.1.Lsh) (t : baseDualV hc n (Pr.vT u) w)
    (ht : ((bc (prV (E := X.E) w) y : GL (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin n) (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun a => inclE (F := X.F) (w.adicCompletion X.F) (z a)) :
    d.1.f P z = fvMeW hc hX hPr u c₀ w P hov (fLoc hc n (Pr.vT u) w t) := by
  have e : (((bc (prV (E := X.E) w) y)⁻¹ : GL (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)).1 *ᵥ
      fun a => inclE (F := X.F) (w.adicCompletion X.F) (z a)) = t.1 := by
    rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h1 := fv_tieL hc n w (basePi_of_ok hX hPr u) Pr.vGs c₀ (sepElt_of_ok hPr u) y hyU d hd P hov (tieInv_spec hPr u P) z hzL
    (by rw [e]; exact t.2)
  rw [h1]
  show _ = (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) * rll_psi hc n w (basePi_of_ok hX hPr u) P.1 t
  congr 2
  exact Subtype.ext e

def levPack_fMe (H : HCrd Pr n fun c => (s c).1.L) (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) :
    (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fM w hw ≃+ (𝓞 X.E ⧸ P.1.asIdeal) := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact fvMeW hc hX hPr u c₀ w P hov

set_option maxHeartbeats 1000000 in

theorem levPack_fv (H : HCrd Pr n fun c => (s c).1.L) (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) (z : Sp X.E n) (hzL : z ∈ (s c).1.Lsh)
    (t : latS (F := X.F) (w.adicCompletion X.F) (intV X.E w)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb)))
    (ht : ((bc (prV (E := X.E) w) ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c :
          GL (Fin H.n') (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) : GL (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun b => inclE (F := X.F) (w.adicCompletion X.F) (Formalism.L2.Forms.reV H.hn.symm X.E z b)) :
    (s c).1.f P z = levPack_fMe hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fT w hw t) := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  refine fv_tieW hc hX hPr u c₀ w P hov _ (ptOfD hc _ (Pr.vT u) Pr.vGs c₀ (s c)).2 (s c)
    (decoOfD_ptOfD hc _ (Pr.vT u) Pr.vGs hS c₀ (s c)) z hzL t ?_
  refine ht.trans ?_
  funext b
  rw [Formalism.L2.Forms.reV_rfl]

set_option maxHeartbeats 1000000 in

theorem levPack_fvQ (H : HCrd Pr n fun c => (s c).1.L) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)
    (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (z : ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (t : latS (F := X.F) (w.adicCompletion X.F) (intV X.E w)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb)))
    (ht : ((bc (prV (E := X.E) w) ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c :
          GL (Fin H.n') (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) : GL (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun b => inclE (F := X.F) (w.adicCompletion X.F) (Formalism.L2.Forms.reV H.hn.symm X.E z.1 b)) :
    (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) = levPack_fMe hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fT w hw t) :=
  (tie_fv hc hPr σ₀ u s Q P c z).trans
    (levPack_fv hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov c z.1 ((tie_Ld_eq hc σ₀ u s Q c).le z.2) t ht)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) (O : AtTOwed a hS hH)

theorem thf_over (u : d.what₂.Word) (w : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.T u : 𝓞 d.X.F) ∈ w.asIdeal) :
    IsOver w ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩).1 := by
  have e : (tieEV d.sp.cm d.hX d.hPr u ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩)).1 = w :=
    congrArg Subtype.val ((tieEV d.sp.cm d.hX d.hPr u).apply_symm_apply ⟨w, h⟩)
  have h1 := tieEV_over d.sp.cm d.hX d.hPr u ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩)
  rwa [e] at h1

theorem thf_pr (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u i)
    (z : ↥(CH.Ld (d.colRec a) u i c)) :
    (hermAtT a hS hH O u).pr i v c z = (levelAgreement a hS hH u i hi).pr v c (hxLd (D := d.colRec a) i hi c z) :=
  hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) i hi v c z

set_option maxHeartbeats 2000000 in

def baseLevelConditions : LevelZeroConditions a hS hH hP hK S hI O := fun u =>
  { frG_lat := fun i v h t =>
      levPack_frLat d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) S (hCrd0 hS u) i v h t
    fM_pi := fun v h x hx m =>
      levPack_fM_pi d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) v h x hx m
    fMe := fun w h =>
      levPack_fMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) w h
        ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) (thf_over u w h)
    fv0 := fun w h c z t ht =>
      (congrArg _ (thf_pr a hS hH O u 0 (Nat.zero_le _) ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) c z)).trans
        (levPack_fvQ d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
          (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) (stepCrd a hS hH u 0 (Nat.zero_le _)) w h
          ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) (thf_over u w h) c (hxLd (D := d.colRec a) 0 (Nat.zero_le _) c z) t ht) }

set_option maxHeartbeats 2000000 in

def formValueAgreement : CH.FvStepTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := fun u i _ hm v =>
  { fb := (levPack_fMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm)
        (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2 v (tieEV_over d.sp.cm d.hX d.hPr u v)).toAddMonoidHom.comp
      ((hermPack hS hP hK u i hm).lev.fT (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2).toAddMonoidHom
    fvI := fun c z t ht =>
      (congrArg _ (thf_pr a hS hH O u i hm v c z)).trans
        (levPack_fvQ d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
          (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm) (stepCrd a hS hH u i hm)
          (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2 v (tieEV_over d.sp.cm d.hX d.hPr u v) c
          (hxLd (D := d.colRec a) i hm c z) t ht) }

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.WithTopLevGTop
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def ChIdx.withTop (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q) : ChIdx X Pr R Q where
  β j := {b : Option (L.β j) // b.isSome = decide (j ≤ m2 + 1)}
  h j b P := match b.1 with
    | some b' => L.h j b' P
    | none => 1
  levG j b := match b.1 with
    | some b' => L.levG j b'
    | none => Λt j
  levQ j b := match b.1 with
    | some b' => L.levQ j b'
    | none => Θt j

variable (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q)

def ChIdx.low {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j) : (L.withTop m2 Λt Θt).β j := ⟨some b, by simp [hj]⟩

def ChIdx.top {j : ℕ} (hj : m2 + 1 < j) : (L.withTop m2 Λt Θt).β j := ⟨none, by simp [Nat.not_le.2 hj]⟩

theorem ChIdx.exists_low {j : ℕ} (hj : j ≤ m2 + 1) (b : (L.withTop m2 Λt Θt).β j) : ∃ b', b = ChIdx.low L m2 Λt Θt hj b' := by
  obtain ⟨b, hb⟩ := b
  cases b with
  | none => simp [hj] at hb
  | some b' => exact ⟨b', rfl⟩

end Top

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XtIntAtQpow
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc1

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem xtEntB {q k₀ c' n' n : ℕ} (hc' : c' = 0) (x : HomE E (n' + c') (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' = x (Loc.eN E (n' + c') p') ⟨p, by omega⟩ := by
  subst hc'
  have hf : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, hf, LocE.scE, Loc.atN, hp, hp']

theorem xtRes {c' n' p' : ℕ} (hp' : p' < n') :
    LinearMap.funLeft E E (Fin.castAdd c') (Loc.eN E (n' + c') p') = (Pi.single (⟨p', hp'⟩ : Fin n') (1 : E) : Sp E n') := by
  funext l
  simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem xtIntAt_qpow (q k : ℕ) : IntAt P ((q : E) ^ k) := by
  refine ⟨(q : 𝓞 E) ^ k, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp

open Classical in

theorem xtLocal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ c' n' n N : ℕ} (hc' : c' = 0)
    (Φ : Loc.SF E K (n' + c') (n + 0))
    (hcongr : ∀ x x' : HomE E (n' + c') (n + 0), (∀ p p', p < n + 0 → p' < n' → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) → Φ x' = Φ x)
    (hint : ∀ x : HomE E (n' + c') (n + 0), Φ x ≠ 0 → ∀ p p', p < n + 0 → p' < n' →
      IntAt P (LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p'))
    (ψ : E → K) (D : ℕ) (hD : 1 ≤ D)
    (psi_add : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → ψ (x + y) = ψ x * ψ y)
    (psi_int : ∀ x : E, IntAt P x → ψ x = 1) (ε : ℤ)
    (prX : Sp E N →ₗ[E] Sp E (n + 0)) (lastN : Sp E N →ₗ[E] E)
    (hsplit : ∀ a : Sp E N, (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prX a i)) ∧ IntAt P (lastN a))
    (zA : HomE E n' N) (zB : HomE E n' (n + 0)) (ηB : Sp E n' →ₗ[E] E)
    (H : ∀ j : Fin n', ((∀ i, IntAt P (zA (Pi.single j 1) i)) ↔ (∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) ∧
      ((∀ i, IntAt P (zA (Pi.single j 1) i)) → (∀ i, redP P (prX (zA (Pi.single j 1)) i) = redP P (zB (Pi.single j 1) i)) ∧
        redP P (lastN (zA (Pi.single j 1))) = redP P (ηB (Pi.single j 1))))
    (y' : Sp E n') (hy : ∀ j, IntAt P ((q : E) * y' j)) :
    Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) =
      Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) := by
  subst hc'
  have hone : IntAt P (-1 : E) :=
    ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := by simpa using xtIntAt_qpow (P := P) q 1
  have hεI : IntAt P (ε : E) :=
    ⟨ε, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hq0 : (q : E) ≠ 0 := by
    intro h0
    apply hu
    have h1 : ((q : ℕ) : 𝓞 E) = 0 := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_natCast, h0, map_zero]
    rw [h1]
    exact Submodule.zero_mem _
  have diff : ∀ a b : E, IntAt P a → IntAt P b → redP P b = redP P a →
      IntAt P ((b - a) / (q : E)) := by
    intro a b ha hb hab
    have hba : IntAt P (b - a) := by
      rw [sub_eq_add_neg]
      exact hb.add (hneg a ha)
    have hr0 : redP P (b - a) = 0 := by
      have h1 := reduction_add hba ha
      rw [sub_add_cancel, hab] at h1
      exact (add_eq_right.1 h1.symm)
    exact ciIntAt_div hq hu hba hr0
  have eX : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        prX (zA (Pi.single ⟨p', hp'⟩ 1)) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have eY : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        zB (Pi.single ⟨p', hp'⟩ 1) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have hexp : ∀ L : Sp E n' →ₗ[E] E, L y' = ∑ j, y' j * L (Pi.single j 1) := by
    intro L
    conv_lhs => rw [show y' = ∑ j, y' j • (Pi.single j (1 : E) : Sp E n') by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul, smul_eq_mul]
  by_cases hall : ∀ j : Fin n', ∀ i, IntAt P (zA (Pi.single j 1) i)
  · have hB := fun j => (H j).1.1 (hall j)
    have hl := fun j => ((hsplit _).1 (hall j)).2
    have hpr := fun j => ((hsplit _).1 (hall j)).1
    have hres := fun j => (H j).2 (hall j)
    rw [if_pos (show ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) from fun i => hl i),
      if_pos (show ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) from fun i => (hB i).2)]
    have hΦ : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) =
        Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) := by
      apply hcongr
      intro p p' hp hp'
      have hpn : p < n := by omega
      rw [eX p p' hpn hp', eY p p' hpn hp']
      refine ⟨_, diff _ _ ((hB ⟨p', hp'⟩).1 ⟨p, by omega⟩) (hpr ⟨p', hp'⟩ ⟨p, by omega⟩)
        ((hres ⟨p', hp'⟩).1 ⟨p, by omega⟩), ?_⟩
      field_simp
      try ring
    rw [hΦ]
    congr 1
    have hΔ : IntAt P ((lastN ∘ₗ zA) y' - ηB y') := by
      rw [hexp (lastN ∘ₗ zA), hexp ηB, ← Finset.sum_sub_distrib]
      refine ciIntAt_sum _ _ fun j _ => ?_
      have e : y' j * (lastN ∘ₗ zA) (Pi.single j 1) - y' j * ηB (Pi.single j 1) =
          ((q : E) * y' j) * (((lastN ∘ₗ zA) (Pi.single j 1) - ηB (Pi.single j 1)) / (q : E)) := by
        field_simp
        try ring
      rw [e]
      exact (hy j).mul (diff _ _ (hB j).2 (hl j) (hres j).2)
    have hqη : IntAt P ((q : E) * ηB y') := by
      rw [hexp ηB, Finset.mul_sum]
      refine ciIntAt_sum _ _ fun j _ => ?_
      rw [← mul_assoc]
      exact (hy j).mul (hB j).2
    have hD' : D = (D - 1) + 1 := by omega
    have h1 : IntAt P ((q : E) ^ D * ((ε : E) * ηB y')) := by
      have e : (q : E) ^ D * ((ε : E) * ηB y') = (ε : E) * (q : E) ^ (D - 1) * ((q : E) * ηB y') := by
        conv_lhs => rw [hD', pow_succ]
        ring
      rw [e]
      exact (hεI.mul (xtIntAt_qpow q (D - 1))).mul hqη
    have h2 : IntAt P ((q : E) ^ D * ((ε : E) * ((lastN ∘ₗ zA) y' - ηB y'))) := by
      rw [← mul_assoc, mul_comm ((q : E) ^ D), mul_assoc]
      exact hεI.mul ((xtIntAt_qpow q D).mul hΔ)
    have e : (ε : E) * (lastN ∘ₗ zA) y' = (ε : E) * ηB y' + (ε : E) * ((lastN ∘ₗ zA) y' - ηB y') := by
      ring
    rw [e, psi_add _ _ h1 h2, psi_int _ (hεI.mul hΔ), mul_one]
  · push_neg at hall
    obtain ⟨j, i, hji⟩ := hall
    have hnA : ¬ ∀ i, IntAt P (zA (Pi.single j 1) i) := fun h => hji (h i)
    have hnB : ¬ ((∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) :=
      fun h => hnA ((H j).1.2 h)
    have hnS : ¬ ((∀ i, IntAt P (prX (zA (Pi.single j 1)) i)) ∧ IntAt P (lastN (zA (Pi.single j 1)))) :=
      fun h => hnA ((hsplit _).2 h)
    have L0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then
          ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) = 0 := by
      by_cases hl : IntAt P (lastN (zA (Pi.single j 1)))
      · have hpx : ¬ ∀ i, IntAt P (prX (zA (Pi.single j 1)) i) := fun h => hnS ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eX p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    have R0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) = 0 := by
      by_cases hl : IntAt P (ηB (Pi.single j 1))
      · have hpx : ¬ ∀ i, IntAt P (zB (Pi.single j 1) i) := fun h => hnB ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eY p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    rw [L0, R0]

end Loc1

end Formalism.L2.Col
end
end

