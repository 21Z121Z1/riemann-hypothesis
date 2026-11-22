import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTensElliptic
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.TraitWit

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem comp_tensφ {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] {r : ℕ} (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem formula_trans (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left}
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) (z : (TK R).left) (J J₀) (hJ : Good D.P.L z J)
    (hJ₀ : Good D.P.L z J₀) (k k₀ : L'.ι) (hk : x.left z ∈ L'.U k) (hk₀ : x.left z ∈ L'.U k₀) :
    gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j =
      (gm x.left z _ (L'.g k k₀))⁻¹ * (gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) *
        ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J₀ ^ W i j) := by
  let H : ((TK R).left ⟶ D.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (D.P.L.g (J ψ) (J₀ ψ))
  let F : Fin r → Fin r → ((TK R).left.presheaf.stalk z)ˣ := fun i j =>
    ∏ a, H (lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ Oε a
  have h₁ := gm_isGen hw x.left z _ _ k k₀ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left) hk hk₀
  have h₂ : gm x.left z _ ((LB.LinComb D.P.L (tensφ pr) (tensε W)).g (fun a => J (x.left ≫ tensφ pr a))
      (fun a => J₀ (x.left ≫ tensφ pr a))) = ∏ i, ∏ j, F i j ^ W i j := by
    refine (gm_linComb D.P.L (tensφ pr) (tensε W) x.left z _ _ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left)).trans ?_
    change ∏ a, H (x.left ≫ tensφ pr a) ^ tensε W a = _
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [comp_tensφ, hx, hx, ← zpow_mul, mul_comm]
    rfl
  have h₃ : ∀ i j, val (D.tau (y i) (y j)) (𝟙 _) z J = (F i j)⁻¹ * val (D.tau (y i) (y j)) (𝟙 _) z J₀ := fun i j => by
    obtain ⟨t, ht, hv⟩ := exists_tau_four D (y i) (y j)
    refine (hv _ _ z J hJ).symm.trans ((gen_trans ht (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans
      (congrArg₂ (· * ·) ?_ (hv _ _ z J₀ hJ₀)))
    change ∏ a, H (𝟙 _ ≫ lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ negε a = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Category.id_comp, ← zpow_neg]
    congr 1
    fin_cases a <;> rfl
  refine (congrArg₂ (· * ·) (h₁.trans (congrArg (· * _ * _) h₂)) (Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun j _ => congrArg (· ^ W i j) (h₃ i j))).trans ?_
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, gv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_psi (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left} (hL : L'.IsLB)
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) :
    ∃ t : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x.left) (fun _ => -1)), t.IsGen ∧
      ∀ z J J', Good D.P.L z J → Good L' z J' → val t (𝟙 _) z J' =
        gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), J' x.left)) *
          ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  let z₀ : (TK R).left := closedPoint (FractionRing R)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good _ D.P.isLB z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J₁, hJ₁, -⟩ := exists_good _ hL z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨t, ht, hv⟩ := exists_gen_val (F := FractionRing R) hL (K := PUnit) (fun _ => x.left) (fun _ => -1) hJ₁
    (gm x.left z₀ _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), J₁ x.left)) *
      ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z₀ J₀ ^ W i j)
  refine ⟨t, ht, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  have a := gen_trans ht (𝟙 (TK R).left) z₀ (hJ'.mem (fun _ : PUnit => x.left) _) (hJ₁.mem (fun _ : PUnit => x.left) _)
  have b : trF (L := L') (fun _ : PUnit => x.left) (fun _ => -1) (𝟙 (TK R).left) z₀ (fun _ => J' (𝟙 _ ≫ x.left))
      (fun _ => J₁ (𝟙 _ ≫ x.left)) = (gm x.left z₀ _ (L'.g (J' x.left) (J₁ x.left)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp]
  exact (a.trans (congrArg₂ (· * ·) b hv)).trans
    (formula_trans D W pr hw x y hx z₀ J J₀ hJ hJ₀ (J' x.left) (J₁ x.left) (hJ' _) (hJ₁ _)).symm

theorem exists_tens [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (hp : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef) (hd : IsUnit (W + W.transpose).det) :
    ∃ D' : DegPre R, D'.P.g = r * D.P.g ∧ Nonempty (Tens D D' W) := by
  obtain ⟨P', pr, hpr, ⟨lim⟩, hg, w, hw⟩ := PowPol.exists_pow_polAV R D.P W hp hd
  obtain ⟨D₀, rfl, -⟩ := GlobalTheory.SelfUnif.exists_degData GlobalTheory.firstFiveLaws.1.cube (maximalIdeal R) P'
  let c : (Fin r → D.X) → (𝟙_ _ ⟶ D₀.toPre.P.A) := fun y => lim.lift (Fan.mk _ fun i => D.c (y i))
  have hc : ∀ y i, c y ≫ pr i = D.c (y i) := fun y i => lim.fac _ ⟨i⟩
  have hx : ∀ y i, (toUnit (TK R) ≫ c y) ≫ pr i = toUnit (TK R) ≫ D.c (y i) := fun y i => by rw [Category.assoc, hc]
  choose ps hps hv using fun y : Fin r → D.X =>
    exists_psi D W D₀.toPre.P.isLB pr hw (toUnit (TK R) ≫ c y) y (hx y)
  refine ⟨{ D₀.toPre with
            X := Fin r → D.X
            addX := inferInstance
            freeX := inferInstance
            finX := inferInstance
            c := c
            c_add := fun a b => lim.hom_ext fun i => ?_
            psi := ps
            psi_gen := hps }, hg,
    ⟨{ pr := pr, pr_hom := hpr, lim := lim, xe := AddEquiv.refl _, c_pr := hc, w := w, w_gen := hw, psi := hv }⟩⟩
  have := hpr i.as
  change c (a + b) ≫ pr i.as = (c a * c b) ≫ pr i.as
  rw [MonObj.mul_comp, hc, hc, hc]
  exact D.c_add _ _

end GlobalTheory.Mum.TraitWit
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

namespace GlobalTheory.MixedLocalChains

section One

variable {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)

def Comm : Prop := ∀ (E E' : M.Z.VDiv) (a : M.Z.Ch), M.Z.capDeg E (M.Z.cD E' * a) = M.Z.capDeg E' (M.Z.cD E * a)

def Cons (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ G : MvPolynomial (Vm D.what₂.Tau N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau N) (dimFl D.what₂.Tau N) →
    ((M.Z.capDeg M.Z.divP (evC M rt G) : ℚ) : ℝ) / (M.cov : ℝ) = chern (collapse D _ (toR G))

def Local : Prop := ∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ m : ℕ, m + k = dimFl D.what₂.Tau N + 1 →
  ∀ Q : MvPolynomial M.Z.LB ℚ, Q.IsHomogeneous m →
    chk (M.lie τ) k (evQ _ Q) + chk (M.om τ) k (evQ _ Q) =
      (∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * chDiv (M.lie (phiPow D (n + 1) τ)).x (k - 1) (evQ _ Q)) -
        chDiv (M.lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)

def LocalFin (o : ℕ) : Prop := ∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ Q : M.Z.Ch,
    (1 - ((p : ℝ) ^ (o * k))⁻¹) * (chk (M.lie τ) k Q + chk (M.om τ) k Q + chDiv (M.lie τ).x (k - 1) Q / ((p : ℝ) - 1)) =
      ∑ n ∈ Finset.range o, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * chDiv (M.lie (phiPow D (n + 1) τ)).x (k - 1) Q

end One

def Pin {p : ℕ} [Fact p.Prime] (W : ValuationSubring ℂ) (jc : KW p →+* ℂ) : Prop :=
  ∀ a : KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (KW p)).range

structure Term {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB) : Prop where
  sum_w : ∑ la, w la = 1
  lie : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).lie (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))
  om : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (Y.N - rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = Y.j + i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).om (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))

def Roots {D : D7} {p : ℕ} [Fact p.Prime] {N j : ℕ} (jc : KW p →+* ℂ) (M : DV.Mdl D p N (rkOf (PsiOf D jc) N j))
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) : Prop :=
  ∀ (t : D.what₂.Tau) (τ : Emb D p), jc.comp τ = tauEmb D t →
    (∀ (i : Fin (rkOf (PsiOf D jc) N j τ)) (i' : Fin N), (i' : ℕ) = i →
      rt (false, (t, i')) = (M.lie τ).x i ∧ rt (true, (t, i')) = (M.lie τ).x' i) ∧
    ∀ (i : Fin (N - rkOf (PsiOf D jc) N j τ)) (i' : Fin N), (i' : ℕ) = j + i →
      rt (false, (t, i')) = (M.om τ).x i ∧ rt (true, (t, i')) = (M.om τ).x' i

def GlobAt {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

theorem globalHeightBound_iff_atGoodPrimes {D : D7} (Y : ShimX D.what₂.Tau) : GlobalTheory.CovHt.DeRhamMinusHodgeTateGoodPrimesAt Y ↔
    ∀ p : ℕ, p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → GlobAt Y p :=
  ⟨fun h p a b c d Sx R => h Sx R p a b c d, fun h Sx R p a b c d => h p a b c d Sx R⟩

section Pairs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O}

def IsCk {E E' : B.X.Modules} (φ : B.GenIso E E') (r k : ℕ) (f : PicSym B.X →ₗ[ℚ] ℚ) : Prop :=
  ∀ M : Vert.Model.FlagModel φ r, GlobalTheory.IsNormalScheme M.B.X → M.relDim = 0 → ∀ Q : PicSym B.X,
    ck (M.toFPair p) k (picSymPull M.π.f Q) = M.π.fibreDeg 1 * f Q

def ckP {E E' : B.X.Modules} (φ : B.GenIso E E') (r k : ℕ) : PicSym B.X →ₗ[ℚ] ℚ :=
  Classical.epsilon (IsCk p φ r k)

variable (B) in

structure Pres where
  r : ℕ
  E : B.X.Modules
  E' : B.X.Modules
  vb : GlobalTheory.VB.IsVB E r
  vb' : GlobalTheory.VB.IsVB E' r
  ψ : E' ⟶ E
  iso : IsIso (B.genRes.map ψ)

def Pres.mod (P : Pres B) : B.X.Modules := cokernel P.ψ

def Pres.ck (P : Pres B) (k : ℕ) : PicSym B.X →ₗ[ℚ] ℚ := haveI := P.iso; ckP p (Vert.Model.GenIso.ofHom P.ψ) P.r k

def Kills (g : Γ(B.X, ⊤)) (F : B.X.Modules) : Prop := smulHom F g = 0

def IsRootOfP (g : Γ(B.X, ⊤)) (a : ℕ) : Prop := ∃ u : Γ(B.X, ⊤)ˣ, g ^ a = u * (p : Γ(B.X, ⊤))

variable (B) in

def fibI : B.X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {(p : Γ(B.X, ⊤))})

def IsFrob (F F' : B.X.Modules) : Prop := ∃ h : (p : Γ((fibI p B).subscheme, ⊤)) = 0,
  Nonempty (F' ≅ (Scheme.Modules.pushforward (fibI p B).subschemeι).obj ((Scheme.Modules.pullback
    (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι)).obj F))

def IsExt (F₁ F₂ F₃ : B.X.Modules) : Prop := ∃ S : ShortComplex B.X.Modules, S.ShortExact ∧
  Nonempty (S.X₁ ≅ F₁) ∧ Nonempty (S.X₂ ≅ F₂) ∧ Nonempty (S.X₃ ≅ F₃)

variable (B) in

structure Chain {ι : Type} (φ : ι → ι) (o : ℕ) where
  π : Γ(B.X, ⊤)
  g : Γ(B.X, ⊤)
  π_root : IsRootOfP p π (p - 1)
  g_root : IsRootOfP p g p
  lw : ι → Pres B
  wl : ∀ τ, (lw τ).E ⟶ (lw τ).E'
  lw_wl : ∀ τ, (lw τ).ψ ≫ wl τ = smulHom _ π
  oo : ι → Pres B
  q : ℕ → ι → Pres B
  l : ℕ → ℕ → ι → Pres B
  c3 : ∀ τ, IsExt (cokernel (wl τ)) (q 0 τ).mod (oo τ).mod
  step : ∀ n < o, ∀ τ, IsExt (q (n + 1) τ).mod (q n τ).mod (l n 0 τ).mod
  l_frob : ∀ n < o, ∀ i ≤ n, ∀ τ, Kills g (l n i τ).mod ∧ IsFrob p (l n i τ).mod (l n (i + 1) τ).mod
  l_last : ∀ n < o, ∀ τ, Nonempty ((l n (n + 1) τ).mod ≅ cokernel (smulHom (lw (φ^[n + 1] τ)).E' (p : Γ(B.X, ⊤))))
  q_frob : ∀ n < o, ∀ τ, Kills g (q (n + 1) τ).mod ∧ IsFrob p (q (n + 1) τ).mod (q n (φ τ)).mod

def Reads {Z : ITh} {r : ℕ} (F : FPair Z r) (a : Z.Ch → PicSym B.X) (b : Z.VDiv → B.VDivQ) {E E' : B.X.Modules}
    (φ : B.GenIso E E') : Prop :=
  ∃ P : Vert.Model.FlagPair φ r, ∀ i, a (Z.c1 (F.x i)) = (B.toITh p).c1 ((P.toFPair p).x i) ∧ b (F.Dv i) = (P.toFPair p).Dv i

end Pairs

def HasChain {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (o : ℕ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (phiPow D (p := p) 1) o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧ ∀ τ,
      (Ch.lw τ).r = rkOf (PsiOf D jc) N j τ ∧ (Ch.oo τ).r = N - rkOf (PsiOf D jc) N j τ ∧
      Reads p ((mdlOf z jc).lie τ) (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw τ).iso; (Vert.Model.GenIso.ofHom (Ch.lw τ).ψ).symm) ∧
      Reads p ((mdlOf z jc).om τ) (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo τ).iso; Vert.Model.GenIso.ofHom (Ch.oo τ).ψ)

def AtGood (Q : ∀ (D : D7) (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (_ : KW p →+* ℂ) (_ : AdmAt O.S O.κ (Fact.out : p.Prime) hW), Prop) : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ O.Y.lev →
    ∀ (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (jc : KW p →+* ℂ), Pin W jc →
      ∀ z : AdmAt O.S O.κ (Fact.out : p.Prime) hW, Q D O p W hW jc z

def ChainSt : Prop := AtGood fun _ _ _ _ _ _ jc z => ∀ o, HasChain z jc o

def LocalSt : Prop := AtGood fun _ _ _ _ _ _ jc z => Local (mdlOf z jc)

def ConsSt : Prop := AtGood fun _ O _ _ _ _ jc z => Cons (mdlOf z jc) (rootOf z jc) O.Y.chern

def TermSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ O.Y.lev →
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (W : ι → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : ι → (KW p →+* ℂ)) (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)), (∀ la, Pin (W la) (jc la)) ∧
    Term O.Y p w jc (fun la => mdlOf (z la) (jc la)) (fun la => rootOf (z la) (jc la))

end GlobalTheory.MixedLocalChains

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def fnF (F : Type) [Field F] [Algebra (FractionRing R) F] (c : F) : Γ((TFK (R := R) F).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

structure Eqv (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ)
    (lab : QkPt D F N → (TFK (R := R) F ⟶ A.A)) (E : Fam D F N → SecK A.L (snd (TFK (R := R) F) A.A).left N) : Prop where
  bij : Function.Bijective E
  add : ∀ s s' s'' : Fam D F N, (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) →
    ∀ j, (E s'').f j = (E s).f j + (E s').f j
  smul : ∀ (c : F) (s s' : Fam D F N), Fam.IsSmul D F c s s' → ∀ j, (E s').f j = liftFun A.A _ (fnF F c) * (E s).f j
  onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x
  frame : ∀ p : QkPt D F N, ∃ w, GlobalTheory.UT.TXFrame N p w
  lift : ∀ p, ∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N (lab p) θ
  act : ∀ (p : QkPt D F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D F N), GlobalTheory.UT.TXFrame N p w →
    SymLift A.A A.L N N (lab p) θ → PhiRel D F N p w s s' → IsActOf A.A A.L N θ (E s) (E s')

def LabExt {D : DegPre R} {A : PolAV (Sp (FractionRing R))} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : ℕ}
    (em : Kb R →ₐ[FractionRing R] F) (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)) : Prop :=
  ∀ p p', QkExt em.toRingHom p p' → (lab' p').left = spMap em.toRingHom ≫ (lab p).left

def IntFam.Over {I : Ideal R} {D : DegPre R} {k : ℕ} (F₀ : IntFam I D k) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (s : Fam D F k) : Prop :=
  ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (F₀.f α)
    (DegPre.prB D F).left 1

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.ConstLat

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def RelFlag {C : CxSt F} {N : ℕ} (A A' : Fin N → Adl C Y) (p n k : ℕ) : Prop :=
  n ≠ 0 ∧ ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (M M' : ι → Matrix (Fin N) (Fin N) V.X.functionField)
    (c c' : ι → Fin N → V.G.functionFieldˣ) (P Q : Matrix (Fin N) (Fin N) V.X.functionField), genericPoint Y.X ∈ W ∧
    P * Q = 1 ∧ (∀ i j, IsIntegral ℤ ((n : V.X.functionField) * P i j) ∧ IsIntegral ℤ ((n : V.X.functionField) * Q i j)) ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) →
      (∀ i j, RegAt x (M a i j) ∧ RegAt x (M' a i j) ∧ RegAt x ((n : V.X.functionField) * P i j)) ∧
        UnitAt x (M a).det ∧ UnitAt x (M' a).det) ∧
    (∀ a i (z : V.G), V.j z ∈ U a →
      UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i) ∧ UnitAt z (V.φ (genAt (A' i).D (V.π z)) * c' a i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
            Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField)))) ∧
          (A' i).lg v e y =
            Real.log (e.w (valAt z (V.φ (genAt (A' i).D (below y.1)) * (c' a i : V.G.functionField))))) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ i,
          (∀ j, j < i → e.w (valAt (z ≫ V.j) (((M' a)⁻¹ * P * M b) i j)) ≤ e.w (p : AlgebraicClosure F) ^ k) ∧
          e.w (valAt (z ≫ V.j) (((M' a)⁻¹ * P * M b) i i) -
            valAt z ((c' a i / c b i : V.G.functionFieldˣ) : V.G.functionField)) ≤ e.w (p : AlgebraicClosure F) ^ k

theorem RelFlag.ne_zero {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} {p n k : ℕ} (h : RelFlag A A' p n k) : n ≠ 0 :=
  h.1

theorem RelFlag.mono {C : CxSt F} {N : ℕ} {A A' : Fin N → Adl C Y} {p n k k' : ℕ} (h : RelFlag A A' p n k)
    (hk : k' ≤ k) : RelFlag A A' p n k' := by
  obtain ⟨hn, V, W, ι, U, M, M', c, c', P, Q, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨hn, V, W, ι, U, M, M', c, c', P, Q, h₁, h₂, h₃, h₄, h₅, h₆, fun v hv e y hy z yt hz hyt a ha => ?_⟩
  obtain ⟨hl, hab⟩ := h₇ v hv e y hy z yt hz hyt a ha
  have hp : e.w (p : AlgebraicClosure F) ^ k ≤ e.w (p : AlgebraicClosure F) ^ k' :=
    pow_le_pow_of_le_one (e.w.nonneg _) ((e.mem_O _).1 (natCast_mem e.O p)) hk
  exact ⟨hl, fun b hb i => ⟨fun j hj => ((hab b hb i).1 j hj).trans hp, (hab b hb i).2.trans hp⟩⟩

namespace RelEx

theorem valAt_natCast {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (m : ℕ) :
    TrueGeo.valAt y (m : Z.functionField) = m := by
  rw [← map_natCast (algebraMap (Z.presheaf.stalk (below y)) Z.functionField), SmallSec.valAt_algebraMap, map_natCast]

theorem regAt_natCast {Z : Scheme.{0}} [IsIntegral Z] (x : Z) (m : ℕ) : RegAt x (m : Z.functionField) :=
  ⟨m, map_natCast _ _⟩

theorem isUnit_natCast (V : Cover Y) (z : V.G) {m : ℕ} (hm : m ≠ 0) : IsUnit (m : V.G.presheaf.stalk z) := by
  let ψ : F →+* V.G.presheaf.stalk z := (V.G.presheaf.germ ⊤ z trivial).hom.comp
    ((V.π ≫ Y.str).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm).isUnit
  simpa using h.map ψ

theorem natCast_ne_zero_X (V : Cover Y) {m : ℕ} (hm : m ≠ 0) : (m : V.X.functionField) ≠ 0 := by
  intro h
  let z := genericPoint V.G
  have h1 : (m : V.X.presheaf.stalk (V.j z)) = 0 :=
    IsFractionRing.injective _ V.X.functionField (by rw [map_natCast, map_zero, h])
  have h2 := congrArg (V.j.stalkMap z).hom h1
  rw [map_natCast, map_zero] at h2
  exact (isUnit_natCast V z hm).ne_zero h2

def scaled (C : CxSt F) (Y : Var F) (m : ℕ) : Adl C Y :=
  { Adl.triv C Y with lg := fun v e y => (Adl.triv C Y).lg v e y + Real.log (e.w m) }

end RelEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def eigAt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) (k : ℕ) : Sym E →₀ ℤ :=
  match (letters Dw)[k]? with
  | some z => Finsupp.single (a, R, .inl (z.1, (z.2 : ℕ))) s
  | none => 0

def eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => eigAt Dw a R 1 k
  | .inr k => eigAt Dw a R (-1) (Fin.rev k)

theorem eigAt_of_lt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) {k : ℕ} (h : k < (letters Dw).length) :
    eigAt Dw a R s k = Finsupp.single (a, R, .inl ((letters Dw)[k].1, ((letters Dw)[k].2 : ℕ))) s := by
  unfold eigAt
  rw [List.getElem?_eq_getElem h]

@[simp] theorem eigSym_inl (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inl k) = eigAt Dw a R 1 k := rfl

@[simp] theorem eigSym_inr (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inr k) = eigAt Dw a R (-1) (Fin.rev k) := rfl

theorem expo_eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (i : Fin g ⊕ Fin g) :
    expo Dw (eigSym Dw a R i) = expo Dw (wholeSym a R i) := by
  have key : ∀ (s : ℤ) (k : ℕ), expo Dw (eigAt Dw a R s k) = expo Dw (Finsupp.single (a, R, .inr k) s) := by
    intro s k
    funext x
    unfold eigAt expo
    cases h : (letters Dw)[k]? with
    | none => simp [letterOf, h]
    | some z =>
      dsimp only
      rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      have e : letterOf Dw (.inl (z.1, (z.2 : ℕ))) = letterOf Dw (.inr k) := (dif_pos z.2.2).trans h.symm
      dsimp only
      rw [e]
  cases i <;> exact key _ _

end GlobalTheory.ConstLat

end
end

