import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SecPtOrd
section
noncomputable section

open IsLocalRing Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Formalism.L2.Pj

section VV

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

private theorem valV_unit_lemma (u : Vˣ) :
    IsDedekindDomain.HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal V)
      (algebraMap V F (u : V)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hu : (u : V) ∉ (IsDiscreteValuationRing.maximalIdeal V).asIdeal := fun h =>
    (IsLocalRing.mem_maximalIdeal _).mp h u.isUnit
  first
  | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff _).mpr hu
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hu
  | exact le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _)
      (not_lt.mp fun h => hu ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mp h))
  | simpa using hu

private theorem valV_unif_lemma_2 {ϖ : V} (hϖ : Irreducible ϖ) :
    IsDedekindDomain.HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal V)
      (algebraMap V F ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hspan : (IsDiscreteValuationRing.maximalIdeal V).asIdeal = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  first
  | exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hspan
  | simpa using IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hspan

lemma vV_unit_alg (u : Vˣ) : vV V (algebraMap V F (u : V)) = 0 := by
  unfold vV valV
  rw [valV_unit_lemma]
  simp

lemma vV_unif_alg {ϖ : V} (hϖ : Irreducible ϖ) : vV V (algebraMap V F ϖ) = 1 := by
  unfold vV valV
  rw [valV_unif_lemma_2 hϖ]
  simp

lemma vV_pow_gen {x : F} (hx : x ≠ 0) (k : ℕ) : vV V (x ^ k) = k * vV V x := by
  unfold vV valV
  rw [map_pow]
  first
  | rw [WithZero.log_pow, nsmul_eq_mul]; ring
  | rw [WithZero.log_pow]; ring
  | simp [WithZero.log_pow]

lemma vV_alg_of_addVal {v : V} {k : ℕ} (hk : IsDiscreteValuationRing.addVal V v = k) :
    vV V (algebraMap V F v) = k := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hϖ
  have hn : n = k := by
    rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl] at hk
    exact_mod_cast hk
  subst hn
  unfold vV valV
  rw [map_mul, map_pow, map_mul, map_pow, valV_unit_lemma, valV_unif_lemma_2 hϖ, one_mul]
  simp

end VV

section Cover

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem isLocalization_unif (h : IsUnif A ϖ) :
    IsLocalization.Away (algebraMap O ↥(As O A) ϖ) A := by
  constructor
  constructor
  · first
    | (rintro ⟨_, n, rfl⟩; rw [map_pow]; exact h.isUnit.pow n)
    | (rintro _ ⟨n, rfl⟩; rw [map_pow]; exact h.isUnit.pow n)
  · intro x
    obtain ⟨n, hn⟩ := h.denom x
    refine ⟨⟨⟨ϖ ^ n • x, hn⟩, ⟨_, n, rfl⟩⟩, ?_⟩
    first
    | simp [Algebra.smul_def, mul_comm]
    | (show x * (algebraMap O A ϖ) ^ n = ϖ ^ n • x
       rw [Algebra.smul_def, map_pow, mul_comm])
  · intro a b hab
    refine ⟨1, ?_⟩
    rw [Subtype.ext hab]

variable (ζ : Pts O A) [IsDVRAt ζ]
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [Algebra V F]
  [IsFractionRing V F] (ι : Loc ζ →+* V)

def locMap : ↥(As O A) →+* F := (algebraMap V F).comp (ι.comp (algebraMap ↥(As O A) (Loc ζ)))

def AddValPres : Prop :=
  ∀ r : Loc ζ, IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal (Loc ζ) r

variable {ζ ι}

lemma vV_locMap (hι : AddValPres ζ ι) {a : ↥(As O A)} {k : ℕ} (hk : vL ζ a = k) :
    vV V (locMap ζ F ι a) = k := by
  show vV V (algebraMap V F (ι (algebraMap _ (Loc ζ) a))) = k
  exact vV_alg_of_addVal (by rw [hι, ← vL_eq_addVal, hk])

lemma locMap_ne_zero (hι : AddValPres ζ ι) {a : ↥(As O A)} (ha : vL ζ a ≠ ⊤) : locMap ζ F ι a ≠ 0 := by
  intro h0
  apply ha
  have h1 : ι (algebraMap _ (Loc ζ) a) = 0 := by
    have h0' : algebraMap V F (ι (algebraMap _ (Loc ζ) a)) = 0 := h0
    exact IsFractionRing.injective V F (by rw [h0', map_zero])
  rw [vL_eq_addVal, ← hι, h1, IsDiscreteValuationRing.addVal_zero]

lemma locMap_eq_zero {a : ↥(As O A)} (ha : vL ζ a = ⊤) : locMap ζ F ι a = 0 := by
  rw [vL_eq_addVal, IsDiscreteValuationRing.addVal_eq_top_iff] at ha
  show algebraMap V F (ι (algebraMap _ (Loc ζ) a)) = 0
  rw [ha, map_zero, map_zero]

lemma locMap_unif_ne (h : IsUnif A ϖ) (hι : AddValPres ζ ι) : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ≠ 0 := by
  apply locMap_ne_zero (F := F) hι
  rw [vL_eq_addVal]
  intro htop
  rw [IsDiscreteValuationRing.addVal_eq_top_iff] at htop
  obtain ⟨⟨s, hs⟩, hs0⟩ := (IsLocalization.map_eq_zero_iff ζ.asIdeal.primeCompl (Loc ζ) _).mp htop
  apply hs
  have hs0' : (s : A) * algebraMap O A ϖ = 0 := by
    have := congrArg Subtype.val hs0
    simpa using this
  have hs1 : s = 0 := Subtype.ext ((h.isUnit.mul_left_eq_zero).mp hs0')
  rw [hs1]
  exact Ideal.zero_mem _

variable (ζ ι)

def phiAt (h : IsUnif A ϖ) (hι : AddValPres ζ ι) : A →+* F :=
  letI := isLocalization_unif h
  IsLocalization.Away.lift (algebraMap O ↥(As O A) ϖ) (g := locMap ζ F ι) (IsUnit.mk0 _ (locMap_unif_ne (F := F) h hι))

variable {ζ ι}

theorem phiAt_coe (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (a : ↥(As O A)) :
    phiAt ζ F ι h hι (a : A) = locMap ζ F ι a := by
  letI := isLocalization_unif h
  unfold phiAt
  first
  | exact IsLocalization.lift_eq _ a
  | exact IsLocalization.Away.lift_eq _ _ a
  | simp [IsLocalization.Away.lift]

private theorem vV_mul_lemma_4 {V₁ F₁ : Type} [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁]
    [Field F₁] [Algebra V₁ F₁] [IsFractionRing V₁ F₁] {x y : F₁} (hx : x ≠ 0) (hy : y ≠ 0) :
    vV V₁ (x * y) = vV V₁ x + vV V₁ y := by
  unfold vV valV
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

private theorem toE_ordAt_lemma_3 (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (x : A) (m : ℕ) (a : ↥(As O A))
    (ha : (a : A) = ϖ ^ m • x) :
    toE (ordAt ϖ ζ m a) = nval V 1 (phiAt ζ F ι h hι x) := by
  have hu : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ≠ 0 := locMap_unif_ne (F := F) h hι
  have hkey : locMap ζ F ι (algebraMap O ↥(As O A) ϖ) ^ m * phiAt ζ F ι h hι x = locMap ζ F ι a := by
    rw [← phiAt_coe (F := F) h hι a, ha, Algebra.smul_def, map_mul]
    simp only [map_pow]
    rw [← phiAt_coe (F := F) h hι (algebraMap O ↥(As O A) ϖ)]
    rfl
  by_cases hT : vL ζ a = ⊤
  · have h0 : phiAt ζ F ι h hι x = 0 := by
      have h1 := hkey
      rw [locMap_eq_zero (F := F) hT] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hu)
    unfold nval
    rw [if_pos h0]
    unfold ordAt
    rw [hT]
    first
    | rfl
    | simp [toE]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hT
    have hla : locMap ζ F ι a ≠ 0 := locMap_ne_zero (F := F) hι hT
    have hφ : phiAt ζ F ι h hι x ≠ 0 := by
      intro h0
      apply hla
      rw [← hkey, h0, mul_zero]
    have hϖT : vL ζ (algebraMap O ↥(As O A) ϖ) ≠ ⊤ := fun ht => hu (locMap_eq_zero (F := F) ht)
    have hvu : vV V (locMap ζ F ι (algebraMap O ↥(As O A) ϖ)) =
        ((vL ζ (algebraMap O ↥(As O A) ϖ)).toNat : ℤ) :=
      vV_locMap (F := F) hι (ENat.coe_toNat hϖT).symm
    have hva : vV V (locMap ζ F ι a) = k := vV_locMap (F := F) hι hk.symm
    have hv : (m : ℤ) * ((vL ζ (algebraMap O ↥(As O A) ϖ)).toNat : ℤ) + vV V (phiAt ζ F ι h hι x) = k := by
      rw [← hva, ← hkey, vV_mul_lemma_4 (V₁ := V) (pow_ne_zero _ hu) hφ, vV_pow_gen (V := V) hu, hvu]
    have hz : vV V (phiAt ζ F ι h hι x) = (k : ℤ) - m * (ep ϖ ζ : ℤ) := by
      unfold ep
      linarith
    have hord : ordAt ϖ ζ m a = (((k : ℤ) - m * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) := by
      unfold ordAt
      rw [← hk, sub_eq_add_neg, WithTop.coe_add]
      congr 1
    unfold nval
    rw [if_neg hφ, hord, hz]
    first
    | (show ((((k : ℤ) - m * (ep ϖ ζ : ℤ) : ℤ) : ℝ) : EReal) = _
       rw [Nat.cast_one, div_one])
    | simp [toE]
    | rfl

theorem toE_ord_eq (h : IsUnif A ϖ) (hι : AddValPres ζ ι) (x : A) :
    toE (ord ϖ ζ x) = nval V 1 (phiAt ζ F ι h hι x) := by
  have hex : ∃ n : ℕ, ϖ ^ n • x ∈ As O A := h.denom x
  unfold ord
  rw [dif_pos hex]
  exact toE_ordAt_lemma_3 (F := F) h hι x _ _ rfl

end Cover

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThClass
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def thLaValAt (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab w La 1 N P y v

abbrev LevQc (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def phiHat {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → LevQc Dw l, φ x * zetaM c ^ pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

def indPhi {n : ℕ} (x0 : Fin n → LevQc Dw l) : (Fin n → LevQc Dw l) → c.F :=
  open Classical in fun x => if x = x0 then 1 else 0

def BaseFrameShape {n : ℕ} (x0 : Fin n → LevQc Dw l) : Prop :=
  (∀ b : Fin n, Dw.p + Dw.q ≤ b.val → x0 b = 0) ∧
  Submodule.span (𝓞 E) (Set.range fun b : {b : Fin n // b.val < Dw.p + Dw.q} => x0 b.1) = ⊤

section Cls

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def ThClsValAt (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ vc : Cl → S, (∀ k, thLaValAt Xo c nab (w k) (La k) (Nc k) (io (x k)) y (vc k)) ∧
    v = evR Xo c xi y * ∑ k, algebraMap c.F S (vol * ((gam k : c.F))⁻¹ * ep k) * vc k

def IsThCls (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThClsValAt Xo c nab w La Nc gam vol ep io xi x y (f p y)

def GenLat.SplitSupp (H : Host E) (Λ : GenLat E n) : Prop :=
  ∃ m : 𝓞 E, m ≠ 0 ∧ Ideal.span {m} • Λ.La ≤ stdLat E n ∧ Ideal.span {m} • stdLat E n ≤ Λ.La ∧
    ∀ P : Ideal (𝓞 E), P.IsPrime → m ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P

def RepsOK (bad : ℕ) (La : Cl → GenLat E n) (Nc : Cl → ℕ) (gam : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt bad ∧ (La k).TrivAt l.M ∧ (La k).LevOK (Nc k) l.M ∧ 0 < gam k ∧
    GenLat.SplitSupp H (La k)

def ThLaTot (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (k : Cl) (v : Vs) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
    ∃! t : S, thLaValAt Xo c nab (w k) (La k) (Nc k) (io v) y t

theorem existsUnique_thCls (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n)
    (Nc : Cl → ℕ) (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c)
    (h : ThLaTot Xo c nab w La Nc io) (x : Cl → Vs) :
    ∃! f : Rul Xo c, IsThCls Xo c nab w La Nc gam vol ep io xi x f := by
  classical
  refine ⟨fun p y => evR Xo c xi y * ∑ k, algebraMap c.F p.R (vol * ((gam k : c.F))⁻¹ * ep k) *
      (h k (x k) p.R y).choose, ?_, ?_⟩
  · intro p y
    exact ⟨fun k => (h k (x k) p.R y).choose, fun k => (h k (x k) p.R y).choose_spec.1, rfl⟩
  · intro f' hf'
    funext p y
    obtain ⟨vc, hvc, hv⟩ := hf' p y
    rw [hv]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(h k (x k) p.R y).choose_spec.2 (vc k) (hvc k)]

def ThClsInCusp (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (x : Cl → Vs) (f : Rul Xo c), IsThCls Xo c nab w La Nc gam vol ep io xi x f → f ∈ cusp a n

end Cls

def gaStar {n : ℕ} (ga : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB (Dw := Dw) c ℓ.1 ℓ.2.1 (fun j => ga j ℓ.2.2)

def minorPolynomial {n : ℕ} (σ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    MvPolynomial (LtN Dw n) c.F :=
  Matrix.det (Matrix.of fun s b : Fin (i + 1) => X (⟨σ, ⟨s.val, by omega⟩, col b⟩ : LtN Dw n))

def aStep (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  a (σ, i) - (if i + 1 < Dw.mult σ then a (σ, i + 1) else 0)

open Classical in

def pG (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : MvPolynomial (LtN Dw n) c.F :=
  ∏ σ : E →+* ℂ, ∏ i : Fin (Dw.mult σ),
    (if h : i.val + 1 ≤ n then
      (if InPsi H σ then minorPolynomial c σ i.val i.isLt (Fin.castLE h)
        else minorPolynomial c σ i.val i.isLt (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a σ i.val

def idlE (I : Ideal (𝓞 E)) : Submodule (𝓞 E) E := Submodule.map (Algebra.linearMap (𝓞 E) E) I

def EpIs {n : ℕ} (bad : ℕ) (B : Ideal (𝓞 E) → c.F) (epF : Submodule (𝓞 E) (Fin n → E) → c.F) : Prop :=
  ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)),
    (⟨L⟩ : GenLat E n).Unimod → (⟨L⟩ : GenLat E n).TrivAt bad → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) →
    cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ →
    Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc →
    ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
        (Ideal.absNorm cc : ℚ) ∧
      epF L = (B cc)⁻¹ * (q : c.F)

def BAbs (B : Ideal (𝓞 E) → c.F) : Prop :=
  ∀ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ σ : c.F →+* ℂ, ‖σ (B cc)‖ ^ 2 = (Ideal.absNorm cc : ℝ)

section Io

variable {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] [Module (𝓞 c.F) Vs] [IsScalarTower (𝓞 c.F) c.F Vs]

def IoLF (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (cga : Matrix (Fin n) (Fin n) E → c.F)
    (nab0 : Submodule (𝓞 c.F) Vs) (hw : Vs) (pG : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Dw.p + Dw.q ≤ n ∧ Function.Injective io ∧
  LinearMap.range io = Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
    (fun τ i => a (τ, i))) ∧
  (∀ ga : Matrix (Fin n) (Fin n) E, ga.conjTranspose * ga = 1 → ∀ v, io (rho ga v) = cga ga • gaStar c (ga.map (IsCMField.complexConj E)) (io v)) ∧
  hw ∈ nab0 ∧ (∀ s : c.F, s • hw ∈ nab0 → ∃ o : 𝓞 c.F, s = (o : c.F)) ∧ io hw = pG ∧
  harmA (Dw := Dw) c a n ⊆ io '' (nab0 : Set Vs)

def LatPin {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) : Prop :=
  ∀ k (v : Fin n → E), v ∈ (La k).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ Lh k

def HarmInNab {Cl : Type} (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (La : Cl → GenLat E n)
    (nabK : Cl → Submodule (𝓞 c.F) Vs) : Prop :=
  ∀ k, harmL (Dw := Dw) c (La k) a ⊆ io '' (nabK k : Set Vs)

end Io

section Ep

variable {n : ℕ} {Cl : Type}

def EpAbs (La : Cl → GenLat E n) (ep : Cl → c.F) : Prop :=
  ∀ (k : Cl) (σ : c.F →+* ℂ), ‖σ (ep k)‖ ^ 2 *
    (((La k).Ln.toAddSubgroup.addSubgroupOf (La k).La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) = 1

end Ep

section Row

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def OneMod {n : ℕ} (lev : ℕ) (ga : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k lev ∧ ∀ i j, ∃ o : 𝓞 E, (k : E) * (ga - 1) i j = (lev : E) * (o : E)

def ThClsRepIndep (nab : NabV Xo c) (bad lev : ℕ) (w : Cl → (Fin n → LevQ Dw l) → c.F) (gam : Cl → ℕ) (vol : c.F)
    (epF : Submodule (𝓞 E) (Fin n → E) → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (xi : Rul Xo c) : Prop :=
  ∀ (Lh Lh' : Cl → Submodule (𝓞 E) (Fin n → E)) (La La' : Cl → GenLat E n) (Nc Nc' : Cl → ℕ)
    (ga : Cl → Matrix (Fin n) (Fin n) E) (x : Cl → Vs) (f f' : Rul Xo c),
    RepsOK (l := l) bad La Nc gam → RepsOK (l := l) bad La' Nc' gam → LatPin Lh La → LatPin Lh' La' →
    (∀ k, (ga k).conjTranspose * ga k = 1 ∧ OneMod lev (ga k) ∧
      ∀ v : Fin n → E, v ∈ Lh' k ↔ ∃ u ∈ Lh k, v = (ga k).mulVec u) →
    IsThCls Xo c nab w La Nc gam vol (fun k => epF (Lh k)) io xi x f →
    IsThCls Xo c nab w La' Nc' gam vol (fun k => epF (Lh' k)) io xi (fun k => rho (ga k) (x k)) f' →
    f = f'

def ThClsScalar (nab : NabV Xo c) (bad lev : ℕ) (w : Cl → (Fin n → LevQ Dw l) → c.F) (gam : Cl → ℕ) (vol : c.F)
    (epF : Submodule (𝓞 E) (Fin n → E) → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (xi : Rul Xo c) : Prop :=
  ∀ (Lh Lh' : Cl → Submodule (𝓞 E) (Fin n → E)) (La La' : Cl → GenLat E n) (Nc Nc' : Cl → ℕ)
    (z : Cl → E) (x : Cl → Vs) (f f' : Rul Xo c),
    RepsOK (l := l) bad La Nc gam → RepsOK (l := l) bad La' Nc' gam → LatPin Lh La → LatPin Lh' La' →
    (∀ k, z k ≠ 0 ∧ OneMod lev ((z k / IsCMField.complexConj E (z k)) • (1 : Matrix (Fin n) (Fin n) E)) ∧
      ∀ v : Fin n → E, v ∈ Lh' k ↔ ∃ u ∈ Lh k, v = (z k / IsCMField.complexConj E (z k)) • u) →
    IsThCls Xo c nab w La Nc gam vol (fun k => epF (Lh k)) io xi x f →
    IsThCls Xo c nab w La' Nc' gam vol (fun k => epF (Lh' k)) io xi
      (fun k => rho ((z k / IsCMField.complexConj E (z k)) • (1 : Matrix (Fin n) (Fin n) E)) (x k)) f' →
    f = f'

def IsThClsD (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

def OneMapRow {D : D7} (V : HSp D) {σ0 : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ0 r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (LL : IntermediateField ℚ ℂ)
    (Cu : Submodule c.F (Rul Xo c)) (cc : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : AutQ V, ph * thAd t x q =
          ze * cc (dict q.out).1 * (lieFac Dw xr a : ℂ) * jFn V σ0 (rdU U) dict mu (act z f) q)

end Row

end Formalism.L2.Pj
end
end

