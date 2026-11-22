import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.VerticalBoundHeightCompare
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
section
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsBlockVec {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v

variable (k) in

def BlockSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  v ≠ 0 → IsBlockVec χ π.π v →
  (∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))) ∨
  ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) ∧
    t < Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))}

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def RecSupp (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (n s : ℕ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) →
    ∀ g : Weil h, (rc n π).charPol g = ∏ a, (rc (d a) (σ a)).charPol g

def RecUnit (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (χ : kˣ →* ℂˣ) (c : Irr k 1), IsUnitaryChar χ → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    ∀ g : Weil h, ∀ α ∈ (rc 1 c).eig g, ‖α‖ = 1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  {T : WDTie N A} (S : Reading T)

def SuppLaws : Prop := ∀ i w hw, RecSupp (S i w hw).rc

def TypeBlock (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ∀ P, ∃ v, v ≠ 0 ∧ IsBlockVec (S i w hw).mu ((S i w hw).rep P).π v

def BlockSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), BlockSplit (w.adicCompletion E)

variable (N A)

def MuInt : Prop := ∀ (i : N.Loc) (τ : H.E →+* ℂ), ∀ z ∈ A.infG (A.muC i) τ, ∃ m : ℤ, z = (m : ℂ)

def ChiIne : Prop := ∀ (i : N.Loc) (w : PlE H), w ∉ placesOver H.E (N.l i) →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))

def XiOverO : Prop := ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
  ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)}

def RowPoint : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
  ∃ i' : N.Loc, N.j i' = N.j i ∧ N.l i' = N.l i ∧ (∀ w, IsSplitPl H w → A.locW i' σ w = A.locW i σ w) ∧
    (∃ φ : N.O i' ≃+* N.O i, Continuous φ ∧ ∀ z, iotaO N A i (φ z) = iotaO N A i' z) ∧
    ∃ (P : A.AV i') (x : N.X i'), thetaOf N A i' σ P ∧ A.ptV i' P = some x

end GlobalTheory.SplitRead
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD
open scoped TensorProduct

namespace GlobalTheory.WH

section Wd

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

def wd (w : ι → Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun t => ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • (w i ∘ₗ LinearMap.proj (t.erase i))

def pw (f : Module.End k E) : Module.End k (Finset ι → E) := LinearMap.pi fun t => f ∘ₗ LinearMap.proj t

def tD (w : ι → Module.End k E) (κ : Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  wd w + LinearMap.pi fun t => ((-1 : ℤ) ^ t.card) • (κ ∘ₗ LinearMap.proj t)

def tcx (T : ℤ → Finset ι → Submodule k E) (w : ι → Module.End k E) (κ : Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => T (n - s.card) s, tD w κ⟩

def acx (A : Finset ι → Submodule k E) (w : ι → Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => if (s.card : ℤ) = n then A s else ⊥, wd w⟩

def cupE {E' E'' : Type} [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'')
    (a : Finset ι → E) (b : Finset ι → E') : Finset ι → E'' := fun u =>
  ∑ j ∈ u, μ (a (u.filter (· ≤ j))) (b (u.filter (j ≤ ·)))

def vec (v : ι → E) : Finset ι → E := fun t => ∑ i ∈ t, if t.card = 1 then v i else 0

end Wd

section Join

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

def lft (s : Finset (ι ⊕ₗ κ)) : Finset ι := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toLeft

def rgt (s : Finset (ι ⊕ₗ κ)) : Finset κ := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toRight

def uni (I : Finset ι) (J : Finset κ) : Finset (ι ⊕ₗ κ) := (I.disjSum J).map (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding

variable {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

def join (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset (ι ⊕ₗ κ) → E'' :=
  fun s => μ (a (lft s)) (b (rgt s))

def edge1 (a : Finset ι → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (rgt s).card = 1 then a (lft s) else 0

def edge2 (b : Finset κ → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (lft s).card = 1 then b (rgt s) else 0

def lcup (μ : E →ₗ[k] E' →ₗ[k] E'') (x : Finset ι → E) (c : Finset (ι ⊕ₗ κ) → E') : Finset (ι ⊕ₗ κ) → E'' := fun s =>
  ∑ i ∈ lft s, μ (x ((lft s).filter (· ≤ i))) (c (s.filter fun t => toLex (Sum.inl i) ≤ t))

def mixF (A : Finset ι → Finset κ → Submodule k E) (s : Finset (ι ⊕ₗ κ)) : Submodule k E :=
  if (lft s).Nonempty ∧ (rgt s).Nonempty then A (lft s) (rgt s) else ⊥

end Join

section Koszul

variable {k : Type} [Field k] {σ : Type} [LinearOrder σ] {E : Type} [AddCommGroup E] [Module k E]

def kFam (Y : σ → Module.End k E) (u v : Module.End k E) (M : Submodule k E) (q : ℤ) : Submodule k (Finset σ → E) :=
  (⨅ T ∈ {T : Finset σ | (T.card : ℤ) ≠ q}, LinearMap.ker (LinearMap.proj T : (Finset σ → E) →ₗ[k] E)) ⊓
    LinearMap.ker (wd Y) ⊓ Submodule.pi Set.univ fun _ => M.map (u ^ (q - 1).toNat * v)

def ytop (Y : σ → Module.End k E) (m : E) : Finset σ → E := wd Y (Pi.single ∅ m)

end Koszul

section Forms

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def XZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.rTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def YZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.lTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def actZ : K ⊗[ℂ] K →ₐ[ℂ] Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K)))

def MZ (a : ℕ) (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  Submodule.map₂ (TensorProduct.mk ℂ _ _) (omB ℂ K (rB ℂ K x I) (d - a)) (omB ℂ K (rB ℂ K x J) a)

def ctr (τ : DR ℂ K →ₗ[K] K) (w : DR ℂ K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ ((Algebra.linearMap F K).restrictScalars ℂ ∘ₗ
    (Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ ∘ₗ LinearMap.mulLeft ℂ w))

end Forms

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ}

def pr2L (j2 : K →ₐ[ℂ] K') : DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  (GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ

def R2 (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  (integralClosure ((rB ℂ K x J).map j2) K').restrictScalars ℂ

variable [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def RY (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  rB ℂ K' x I ⊔ R2 x j2 J

def gY (j2 : K →ₐ[ℂ] K') : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  TensorProduct.lift ((LinearMap.mul ℂ (DR ℂ K')).compl₁₂ ((GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ) (pr2L j2))

def Val (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (v : K') (c : ℂ) : Prop :=
  ∃ (b : K') (hb : b ∈ B) (hbv : b * v ∈ B), e ⟨b, hb⟩ ≠ 0 ∧ e ⟨b * v, hbv⟩ = e ⟨b, hb⟩ * c

def IsFix (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (j2 : K →ₐ[ℂ] K') (B0 : Subalgebra ℂ K) : Prop :=
  ∀ b ∈ B0, ∀ h1 : algebraMap K K' b ∈ B, Val B e (j2 b) (e ⟨_, h1⟩)

end Y

end GlobalTheory.WH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Dat

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA cB : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

end Dat

section Range

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word}

theorem twDen_pos : 0 < cAof sel mu cst := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _

theorem twMod_pos (hT : 0 < Pr.T u) : 0 < cBof sel mu cst u := Nat.mul_pos hT (pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _)

theorem mem_divLat_of_loc {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j) {x : HomE X.E (R.N i) (R.N j)}
    (h1 : phiT X.K p.deco.1 p'.deco.1 x ≠ 0)
    (h2 : ∀ (P : rowSG Pr sel mu) s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * inFr (frsF sel mu p P) (frsF sel mu p' P) x (Pi.single s 1) l)) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) := by
  classical
  intro P hP y hy
  change ((cAof sel mu cst : ℕ) : 𝓞 X.E) • x y ∈ _
  have hP' : P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := Finset.mem_union.1 hP
  rcases hP' with hT | hB
  · exact Submodule.smul_mem _ _ (cond_of_ite_ne_zero h1 ⟨P, hT⟩ y hy).1
  · obtain ⟨k, hk⟩ : qOf P ^ cst.A ∣ cAof sel mu cst :=
      pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (a := ⟨P, hB⟩) (Finset.mem_univ _)) _
    have h3 := GlobalTheory.Proof.datum_support_div_lattice_interior.smul_mem_of_frames P (p.deco.1.at P) (p'.deco.1.at P) (frsF sel mu p ⟨P, hB⟩) (frsF sel mu p' ⟨P, hB⟩)
      (frsF_mem p ⟨P, hB⟩) (frsF_mem p' ⟨P, hB⟩) x _ (h2 ⟨P, hB⟩) y hy
    rw [hk, Nat.cast_smul_eq_nsmul, mul_comm, mul_smul, ← Nat.cast_smul_eq_nsmul X.E (qOf P ^ cst.A), Nat.cast_pow]
    exact nsmul_mem h3 k

theorem loc_of_mem_mulLat (hPr : Pr.Ok) {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j)
    (x : HomE X.E (R.N i) (R.N j)) {y : HomE X.E (R.N i) (R.N j)}
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    phiT X.K p.deco.1 p'.deco.1 (x + y) = phiT X.K p.deco.1 p'.deco.1 x ∧
      ∀ (P : rowSG Pr sel mu) s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * inFr (frsF sel mu p P) (frsF sel mu p' P) y (Pi.single s 1) l) := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  refine ⟨GlobalTheory.phiT_add_smul_homAt X.K _ _ p'.deco.2 Finset.subset_union_left _ (fun P => ?_) x y₀ hy₀, fun P => ?_⟩
  · rw [cBof, Nat.cast_mul, ← hPr.piT_norm u]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    have h := P.2
    unfold Primes.vT divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  · obtain ⟨r, hr⟩ : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
    exact GlobalTheory.intAt_inFr_smul_homAt (Finset.mem_union_right _ P.2) _ _ (frsF_mem p P) (frsF_mem p' P) _ (r : 𝓞 X.E) _
      (pow_ne_zero _ (GlobalTheory.TopInv.qOf_ne P.1)) (by rw [hr]; simp) y₀ hy₀

variable {m2 : ℕ}

theorem locTop_den (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} {y : HomE X.E (R.N (m2 + 1)) (R.N R.m)}
    {y' : Sp X.E (R.N (m2 + 1))} (h : locTop Ch sel mu cst m2 P y y' ≠ 0) (s : Fin (R.N (m2 + 1))) (l : Fin (R.N R.m)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * y (Pi.single s 1) l) := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  by_cases hl : l.1 < R.N R.m - 1
  · have h3 := GlobalTheory.SuppTop.intAt_of_phiTop Ch mu _ m2 hm P.1 _ h1 l.1 s.1 hl s.2
    have e : Loc.eN X.E (R.N (m2 + 1) + cOf R (m2 + 1)) s.1 = Pi.single (Fin.castAdd _ s) 1 := by
      funext t
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [e, LinearMap.comp_apply, LinearMap.comp_apply, castAdd_single, Loc.atN, dif_pos (show l.1 < R.N R.m - 1 + 0 from hl)] at h3
    exact (intAt_pow (intAt_nat _) _).mul h3
  · have h3 := GlobalTheory.SuppTop.intAt_of_ftY sel mu cst P _ _ h2 s
    obtain rfl : l = Br.iL (N_m_succ R) := Fin.ext (by have := l.2; show l.1 = R.N R.m - 1; omega)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_A
    rw [LinearMap.comp_apply, atNL_last] at h3
    rw [hk, add_comm, pow_add, mul_assoc]
    exact (intAt_pow (intAt_nat _) _).mul h3

open Classical in

theorem locTop_add (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hD : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {z : HomE X.E (R.N (m2 + 1)) (R.N R.m)} {y' : Sp X.E (R.N (m2 + 1))}
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l))
    (hy' : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y' i)) :
    locTop Ch sel mu cst m2 P (y + z) y' = locTop Ch sel mu cst m2 P y y' := by
  simp only [← div_eq_inv_mul] at hz
  unfold locTop
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (GlobalTheory.TopInv.PhiTop_add mu Ch _ m2 hm P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P hD _ _ _ (fun s => ?_) hy')
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; unfold cOf at this; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, castAdd_single, ← pow_one (qOf P.1 : X.E)]
    exact GlobalTheory.TopInv.intAt_div_pow_le (GlobalTheory.TopInv.qOf_ne P.1) hc.B_pos (hz s _)
  · rw [LinearMap.comp_apply, atNL_last]
    exact hz s _

end Range

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {A : Amb X} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
  {P : LevFam X.E X.K R.r Pr.vGs} {c : TopDepth R cst.M} {G : ChGlob X R.m}

variable (A) in

def twThPt (i j : ℕ) (e : j = i + 1) (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β)
    (d : (twFam W Ch sel mu cst L u m2 b hY P c i).D β) (d' : (twFam W Ch sel mu cst L u m2 b hY P c j).D β') :
    VCx X.Tau (R.N i) (R.N j) → ℂ :=
  A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (levPt i β d).deco.1.N (levPt j β' d').deco.1.N (twXi i j e β β' d d')

section Pt

variable (i j : ℕ) (e : j = i + 1) (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β)
  (d : (twFam W Ch sel mu cst L u m2 b hY P c i).D β) (d' : (twFam W Ch sel mu cst L u m2 b hY P c j).D β')

end Pt

theorem twThPt_top (e : R.m = m2 + 1 + 1) (h : m2 + 1 = m2 + 1) (h' : R.m = R.m) (d : (ybCpl W sel mu cst L u m2 b hY).Pts)
    (p' : TopPt R sel mu u) :
    twThPt (Ch := Ch) (P := P) (c := c) A (m2 + 1) R.m e (.cpl h) (.top h') d p' =
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.1.deco.1.N p'.deco.1.N
        (XiTop Ch sel mu cst m2 d.1.1 d.1.2 p') := rfl

section Vec

variable (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (h0 : A.AA ≠ ⊥)
include hPr hL h0

end Vec

abbrev twSec (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : (twFam W Ch sel mu cst L u m2 b hY P c i).D x.1 :=
  ((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2

section Def

variable (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi)

def twTh : (twSrc chi hX hm hF hK hρ).ThFam := fun i x x' => twThPt A i (i + 1) rfl x.1 x'.1 (twSec i x) (twSec (i + 1) x')

def twChain : ColumnChain R X.Tau (W.hc u) := (twSrc chi hX hm hF hK hρ).chainTh A.σ₀ (W.hc u) A.cD (twTh chi hX hm hF hK hρ)

end Def

def twChainOf {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok)
    (hχ : TaylorLogMetric.IsChi D χ) (hF : ∀ j, (chF W sel mu L u j).Ok) (hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c) :
    ColumnChain R X.Tau (W.hc u) :=
  twChain (chiLat s χ) hX hL.hm hF hK (rhoUnit_of hX hPr hsel hS ht hL hG hs hχ)

variable (W sel mu cst A u) in

def TwJets : Prop :=
  ∀ i < R.m, JetsRatDeg A (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) fun τ => ∑ a, (W.nuW u (i + 1) τ).w a

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

theorem twChain_unf (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) (x' : (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl)
    (Q : Formalism.L2.DIV.Pol ℂ X.Tau (R.N i)) (y' : ChSrc.Fr X A.σ₀ (R.N (i + 1))) :
    (twChain chi hX hm hF hK hρ).unf i x x' (fun y : ChSrc.Fr X A.σ₀ (R.N i) => MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q) y' =
      ∑ q ∈ (derPol A.cD Q y'.1).support, MvPolynomial.coeff q (derPol A.cD Q y'.1) * derivAt0 (twTh chi hX hm hF hK hρ i x x') q :=
  (twSrc chi hX hm hF hK hρ).chainTh_unf A.σ₀ (W.hc u) A.cD _ i x x' Q y'

variable (hT : 0 < Pr.T u) (hχ : ChiSplit chi A) (hs : ∀ i < R.m, A.ESmooth (R.N i) (R.N (i + 1))) (hJ : TwJets W sel mu cst A u)
include hT hχ hs hJ

end Laws

section Same

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Same

section Of

variable {D : D7} {s : Seam D X} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Base D cc δ} {χ : TaylorLogMetric.IdE D → ℂ} {cD : D.what₂.Tau → ℂ}
  {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} {hX : X.Ok} {hPr : Pr.Ok} {hsel : IsSel X sel}
  {hS : ∀ i, Pr.g i ∈ S} {ht : Ch.Tied s.σ₀ e G.mu0 eta} {hL : L.Ok Ch sel mu cst G m2} {hG : G.σ₀ = s.σ₀} {hs : s.Ok}
  {hχ : TaylorLogMetric.IsChi D χ} {hF : ∀ j, (chF W sel mu L u j).Ok} {hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c}

end Of

example {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
    {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} (i : ℕ)
    (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) (x' : (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl)
    (y' : ChSrc.Fr X A.σ₀ (R.N (i + 1))) :
    (twChain chi hX hm hF hK hρ).unf i x x' (fun _ => 1) y' = twTh chi hX hm hF hK hρ i x x' 0 := by
  have h := twChain_unf (chi := chi) (hX := hX) (hm := hm) (hF := hF) (hK := hK) (hρ := hρ) i x x' 1 y'
  simp only [map_one, derPol] at h
  refine h.trans ?_
  rw [MvPolynomial.support_one, Finset.sum_singleton, MvPolynomial.coeff_zero_one, one_mul, derivAt0]
  have h0 : ∀ n, n = 0 → ∀ v, iteratedFDeriv ℂ n (twTh chi hX hm hF hK hρ i x x') 0 v = twTh chi hX hm hF hK hρ i x x' 0 := by
    rintro _ rfl v
    exact iteratedFDeriv_zero_apply v
  exact h0 _ (by simp) _

example [IsEmpty (rowSG Pr sel mu)] (e : R.m = m2 + 1 + 1) (d : (ybCpl W sel mu cst L u m2 b hY).Pts) (p' : TopPt R sel mu u) :
    twThPt (Ch := Ch) (P := P) (c := c) A (m2 + 1) R.m e (.cpl rfl) (.top rfl) d p' =
      A.thDat (Sall sel mu u) 1 (Pr.T u) d.1.1.deco.1.N p'.deco.1.N (phiT X.K d.1.1.deco.1 p'.deco.1) := by
  rw [twThPt_top, cAof, cBof, Fintype.prod_empty, one_pow, one_pow, mul_one]
  congr 1
  funext x
  unfold XiTop
  rw [Fintype.prod_empty, mul_one]

example (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m ≤ i) : IsEmpty (twFam W Ch sel mu cst L u m2 b hY P c (i + 1)).Cl :=
  ⟨fun x => (SpIdx.isEmpty_of_lt (by omega) (by omega)).false x.1⟩

end Chain

example {D : D7} {EX : ErrX D} (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    (A : Amb (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recFields D)) (ξ : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.Twist D)
    (cst : LocCst (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recFields D) (rowSG (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recPrimes EX) sel ξ)) (u : D.what₂.Word) :
    TwJets (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recWts EX) sel ξ cst A u ↔ GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.FieldTie sel A ξ cst u := Iff.rfl

end GlobalTheory.GO
end
end

