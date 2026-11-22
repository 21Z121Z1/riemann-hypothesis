import Formalism.LocalToGlobal.Columns.Bundle0023
import Formalism.LocalToGlobal.Columns.TiedCG
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
import Mathlib
import Formalism.LocalToGlobal.Columns.ChainInstY

-- bundled from Formalism.LocalToGlobal.Columns.TiedVal
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatSpanG {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def IntSpanG {K : Type} [Field K] (s : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW Pl w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

structure ValCrd (σ₀ : X.K →+* ℂ) (u : Pr.Word) (i : ℕ) extends
    StepCrd Pr σ₀ (R.N i) (fun c : StCl W Λ u i => ((stepGSD W Λ u i).outSec.rep c).1.L) where
  lt : X.Tau → DomWeight (R.N i)
  hlt : lt = W.lamTrue u i

variable (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ) (c₀ : DiaG X.E (Pr.vT u)) (hS : DecoPtSurj hc (R.N i) (Pr.vT u) Pr.vGs)

@[reducible] def valK (Q : ValCrd W Λ σ₀ u i) :=
  clsG hc hX hPr σ₀ u (Λ i) c₀ (fun c : StCl W Λ u i => (stepGSD W Λ u i).outSec.rep c) hS
    (fun c => (stepGSD W Λ u i).outSec.spec c) Q.toStepCrd

def valEY (Q : ValCrd W Λ σ₀ u i) : FrS X σ₀ (R.N i) ≃ Frames (gramC Q.J Q.emb) := Equiv.refl _

namespace Val

def De (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∃ C : GL (Fin (R.N i)) X.E, cT (hc.sig : X.E →+* X.E) C.1 * C.1 = Q.J ∧
    (∀ x : Fin (R.N i) → X.E, x ∈ Q.l0 ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 X.E) X.E).range) ∧
    ∀ τ (z : FrS X σ₀ (R.N i)), deFr z τ = Q.emb τ C.1.det * ((valEY W Λ σ₀ u i Q z).1 τ).det

def Fi (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ φ : StCl W Λ u i → FrS X σ₀ (R.N i) → ℂ, φ ∈ (stepEv W Λ σ₀ hσ u i).Fi ↔
    (fun c z => φ c ((valEY W Λ σ₀ u i Q).symm z)) ∈
      FiC (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev Q.emb Q.lt (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y

def IpV (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (o : Frames (gramC Q.J Q.emb)), o.IsON → ∀ P ∈ CSpan (W.lamN u i), ∀ P' ∈ CSpan (W.lamN u i),
    (stepEv W Λ σ₀ hσ u i).ip
      (fun z => fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) P (valEY W Λ σ₀ u i Q z))
      (fun z => fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) P' (valEY W Λ σ₀ u i Q z)) =
    nfAll (W.lamN u i) P' P

def Rat (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ φ : StCl W Λ u i → FrS X σ₀ (R.N i) → ℂ, (∃ x, (stepEv W Λ σ₀ hσ u i).emb x = φ) ↔
    φ ∈ (stepEv W Λ σ₀ hσ u i).Fi ∧ ∀ c, ∃ P ∈ RatSpanG σ₀ (W.lamN u i),
      ∀ z, φ c z = fnOf _ (shiftOf Q.lt) 1 P (valEY W Λ σ₀ u i Q z)

def Lat (Pl : Rows.Places X.K) (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ x : (stepGSD W Λ u i).EqFun, x ∈ (stepGSD W Λ u i).intDel ↔
    ∀ (w : Pl.Pl) (c : StCl W Λ u i) (B : GL (Fin (R.N i)) X.E),
      IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) B →
      ∃ P ∈ IntSpanG σ₀ Pl w (W.lamN u i),
        ∀ z, (stepEv W Λ σ₀ hσ u i).emb x c z =
          fnOf _ (shiftOf Q.lt) (atInf Q.emb (B⁻¹ : GL (Fin (R.N i)) X.E).1) P (valEY W Λ σ₀ u i Q z)

variable (eV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal})

def Dil (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (v : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ v.1.asIdeal)ˣ) (k : ℤ), (k : 𝓞 X.E ⧸ v.1.asIdeal) = a → ∀ c δ,
    IsDia (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) v a c)) :
      Cls (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev) = Quotient.mk'' ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c * δ)

def DilT (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (v : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ v.1.asIdeal)ˣ) (k : ℤ), (k : 𝓞 X.E ⧸ v.1.asIdeal) = a → ∀ c δ,
    IsDia (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev (eV v).1 (eV v).2 k δ →
    ∀ g ∈ AdFun (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev Q.emb,
    (stepEv W Λ σ₀ hσ u i).trPt ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dia1 v a)
      (fun z => g ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) v a c))
        (valEY W Λ σ₀ u i Q z)) =
      fun z => g ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c * δ) (valEY W Λ σ₀ u i Q z)

end Val

theorem lamTrue_eq_shW (u : Pr.Word) (i : ℕ) :
    W.lamTrue u i = fun τ => shW (W.lamN u i τ) ((i * (R.t + 1) / 2 : ℕ) : ℤ) := by
  funext τ
  have h : ((i * (R.t + 1) / 2 : ℕ) : ℤ) = (i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
    obtain ⟨b, hb⟩ := R.t_odd
    have h2 : R.t + 1 = 2 * (b + 1) := by omega
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    push_cast
    ring
  unfold Wts.lamTrue shiftW shW
  congr 1
  funext x
  rw [h]
  ring

theorem Val.de (Q : ValCrd W Λ σ₀ u i) : Val.De W Λ hc σ₀ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  refine ⟨1, ?_, ?_, ?_⟩
  · simp [cT]
  · intro x
    simp only [Units.val_one, Matrix.one_mulVec]
    constructor
    · intro hx a
      exact Submodule.mem_one.1 (hx a trivial)
    · intro hx a _
      exact Submodule.mem_one.2 (hx a)
  · intro τ z
    simp only [Units.val_one, Matrix.det_one, map_one, one_mul]
    rfl

theorem Val.ipV (Q : ValCrd W Λ σ₀ u i) : Val.IpV W Λ σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro o ho P _ P' _
  have h := ipFr_fnOf (gramC (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) (embAt σ₀ X.emb)) (W.lamTrue u i) (stdFrC _) o
    (fun τ => by simp [stdFrC, gramC]) (frame_std _ o ho) P P'
  have h2 : nfAll (W.lamTrue u i) P' P = nfAll (W.lamN u i) P' P := by
    rw [lamTrue_eq_shW]
    exact nfAll_shW _ _ _ _
  rw [← h2]
  exact h

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem lamT_eq (u : d.what₂.Word) (i : ℕ) : CF.lamT (D := d.colRec a) u i = d.W.lamTrue u i :=
  (lamTrue_eq_shW (Pr := d.Pr) d.W u i).symm

def valCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    ValCrd (Pr := d.Pr) d.W d.lev d.σ₀ u i where
  toStepCrd := stepCrd a hS hH u i hi
  lt := CF.lamT (D := d.colRec a) u i
  hlt := lamT_eq a u i

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
  (eV : ((d.colRec a).mem u).A.vT ≃ CF.PlT (d.colRec a) u)

def valuationAgreement
    (hFi : Val.Fi (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (valCrd a hS hH u i hi))
    (hRat : Val.Rat (Pr := d.Pr) d.W d.lev d.σ₀ d.star_cx u i (valCrd a hS hH u i hi))
    (hLat : Val.Lat (Pr := d.Pr) d.W d.lev d.sp.cm d.σ₀ d.star_cx u i d.what₂.places (valCrd a hS hH u i hi))
    (hDil : Val.Dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi))
    (hDilT : Val.DilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi)) :
    CF.ValTied (D := d.colRec a) u eV i hi (classAgreement a hS hH hP u i hi) where
  eY := valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi)
  de := Val.de (Pr := d.Pr) d.W d.lev d.sp.cm d.σ₀ u i (valCrd a hS hH u i hi)
  Fi := hFi
  ipV := fun _ => Val.ipV (Pr := d.Pr) d.W d.lev d.σ₀ d.star_cx u i (valCrd a hS hH u i hi)
  rat := hRat
  lat := hLat
  dil := hDil
  dilT := hDilT

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXp
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_basePi_one : BasePi (∅ : Finset (Pl X.E)) (1 : 𝓞 X.E) where
  dvd r := ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩
  cop := isCoprime_one_left

theorem xp_L_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (Pl E)}
    (d : Deco E n (∅ : Finset (Pl E)) SG) : d.L = d.N := by
  unfold Deco.L
  have : {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (Pl E)), d.f P x = 0} = (d.N : Set (Sp E n)) := by
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty P.1)⟩
  rw [this, Submodule.span_eq]

def tieLevP : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)

def clsPG₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  lev := tieLevP hc σ₀ Λ
  y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
  y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
  y_lat := fun c x => by
    have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
    rw [xp_L_eq_N] at h
    exact h
  stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
  stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range c γ.1 γ.2

def clsPG (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    ClsG hc.sig Q.J 1 Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsPG₁ hc σ₀ Λ s hS hs

end GenP

section Rec

variable {d : ColDat} (a : ColArgs d)

abbrev PCl (d : ColDat) : Type := (ptGSD (Pr := d.Pr) d.W d.levP).Cl

def ColDat.reprP (d : ColDat) (c : PCl d) : DecoSet d.X.E (d.R.N d.R.m - 1) ∅ d.Pr.vGs :=
  (ptGSD (Pr := d.Pr) d.W d.levP).outSec.rep c

def crdPr (hS : SpStd d.toColBase) (hH : HostHyp d) :
    StepCrd d.Pr d.σ₀ (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  J := CF.gramP (d.colRec a)
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := fun c => (d.reprP c).1.N
  l0 := stdLat d.X.E (d.R.N d.R.m - 1)
  hJ := gramP_eq a hS
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := rfl
  hl0 := rfl

def PtSurjP (d : ColDat) : Prop := DecoPtSurj d.sp.cm (d.R.N d.R.m - 1) (∅ : Finset (Pl d.X.E)) d.Pr.vGs

def pClsG (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) :=
  clsPG d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH)

def parabolicClassAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    CF.ClsPTied (D := d.colRec a) u where
  lev := (pClsG a hS hH hP).lev
  y := (pClsG a hS hH hP).y
  y_bij := (pClsG a hS hH hP).y_bij
  lat := fun c => (d.reprP c).1.N
  y_lat := (pClsG a hS hH hP).y_lat
  lat_fin := fun c => Module.Finite.iff_fg.2 (d.reprP c).2.lat.fg
  stabI := (pClsG a hS hH hP).stabI
  stabI_inj := (pClsG a hS hH hP).stabI_inj
  stabI_range := (pClsG a hS hH hP).stabI_range

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XiRef
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Yb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOf (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : Set (Sp E n) :=
  {z | ∀ w : SG, (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w}

def Deco.y0 (d : Deco E n ST SG) (k : ℕ) : Set (Sp E n) := d.yOf fun w => Loc.eN (𝓞 E ⧸ w.1.asIdeal) n k

end Yb

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

variable {sel mu} in

def liftQ (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E n ST SG) :
    DecoF X.E n ST SG (QE sel (mu : Chr X.F X.E X.K)) :=
  ⟨(p, fun _ => 1), fun P _ => absurd (hQ ▸ P.2 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)⟩

def XiRef {u : Pr.Word} (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if h : i < m2 then XiEntry Ch sel mu cst L i (al i (by omega)) (al (i + 1) (by omega)) p p' x
  else if h' : i = m2 then XiCpl1 Ch sel mu cst L i (al i (by omega)) p p' (p'.deco.1.y0 R.k) x
  else if i = m2 + 1 then XiTop Ch sel mu cst i p (p.deco.1.y0 R.k) p' x
  else 0

def refK {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (al : ∀ j, j ≤ m2 + 1 → L.β j) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) :
    (colValF W sel mu u i).V →ₗ[X.K] (colValF W sel mu u (i + 1)).V :=
  kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
    p'.deco.1.N (frsF sel mu p') (XiRef Ch sel mu cst L m2 al i p p')

end Ref

end Formalism.L2.Col
end
end

