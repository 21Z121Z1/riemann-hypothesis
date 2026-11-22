import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.WeilDatumUniqueOfDeterminants
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices

namespace OrthogonalPartDecomposition

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

theorem res_eq {Xg : Finset (G → K)} {Sg Sg' : Pl0 → K[X]} (h : Sg ∈ B.resSet Xg) (h' : Sg' ∈ B.resSet Xg)
    {x : B.Pl × ℕ → K} (hx : B.HasRes Sg x) (hx' : B.HasRes Sg' x) : Sg = Sg' := by
  funext P0
  by_cases hP : P0 ∈ Set.range B.pl
  · obtain ⟨P, rfl⟩ := hP
    exact mul_right_cancel₀ (B.blockProd_ne_zero P) ((hx P).symm.trans (hx' P))
  · rw [h.1 P0 hP, h'.1 P0 hP]

theorem map_conjTranspose_of_mem_cmMax {n d : ℕ} (σ : K →+* ℂ) (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, E i a ∈ cmMax K) :
    (Eᴴ).map σ = (E.map σ)ᴴ :=
  map_conjTranspose' σ E fun i a => ConjugateWeightGram.isCMSub_cmMax σ _ (hE i a)

theorem HV_map (h : BlockHyp B ℓ v0 s) (σ : K →+* ℂ) :
    (B.HV ℓ).map σ = σ (Nat.card ℓ.P : K)⁻¹ • (((B.vE ℓ).map σ)ᴴ * B.S.H.map σ * (B.vE ℓ).map σ) := by
  have e : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [e, ← map_conjTranspose_of_mem_cmMax σ _ (hv_spec h).1, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem adjC (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (σ : K →+* ℂ) (i : B.Pl × ℕ) :
    ∃ i', (B.HV ℓ).map σ * (tV B ℓ i).map σ = ((tV B ℓ i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := opMat_adj hH i
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v0)
  have h2 : B.S.H * B.opMat i = (B.opMat i')ᴴ * B.S.H := by
    have := congrArg Matrix.conjTranspose hi'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
    exact this
  have h2' : B.S.H.map σ * (B.opMat i).map σ = ((B.opMat i').map σ)ᴴ * B.S.H.map σ := by
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax σ _ (hH.rat i')]
  have hT : ∀ k, (B.vE ℓ).map σ * (tV B ℓ k).map σ = (B.opMat k).map σ * (B.vE ℓ).map σ := by
    intro k
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  refine ⟨i', ?_⟩
  rw [HV_map h σ]
  exact adj_transfer _ _ _ _ _ _ _ (hT i) (hT i') h2'

theorem part_orth (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (v : InfinitePlace K)
    {Sg Sg' : Pl0 → K[X]} (hSS : ∀ x, B.HasRes Sg' x → ¬ B.HasRes Sg x)
    {x y : Fin (B.dZ ℓ Z) → K} (hx : x ∈ B.part ℓ Z Sg) (hy : y ∈ B.part ℓ Z Sg') :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = 0 := by
  classical
  have hpq := (pq_orth (Z := Z) h).1
  have hsurj : Function.Surjective (B.Pq ℓ Z).mulVec := fun w =>
    ⟨(B.zE ℓ Z) *ᵥ w, by rw [Matrix.mulVec_mulVec, hpq, Matrix.one_mulVec]⟩
  have hA : ((B.HV ℓ).map v.embedding).PosDef := (hv_spec h).2.2 v
  have hQ : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ hA).1 _ (map_surj v.embedding _ hsurj)
  have hmet : metOf (B.XQ ℓ Z v) = quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding) :=
    (frameOfSpec _ _ hQ).2
  have hR : IsUnit (((B.Pq ℓ Z).map v.embedding) * ((B.HV ℓ).map v.embedding)⁻¹ *
      ((B.Pq ℓ Z).map v.embedding)ᴴ).det := by
    have : IsUnit (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).det :=
      isUnit_iff_ne_zero.2 hQ.det_pos.ne'
    rwa [quotMetC, Matrix.isUnit_nonsing_inv_det_iff] at this
  have hc : Col.PairComm (linF fun i => (tV B ℓ i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, tV_comm h])
  have hs : Col.SplitOver (linF fun i => (tV B ℓ i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hcf : Col.PairComm (linF fun i => (B.opMat i).map v.embedding) := fun i j =>
    linF_commute (by rw [← Matrix.map_mul, ← Matrix.map_mul, opMat_comm h.ok.comm])
  have hvv : B.vPr ℓ * B.vE ℓ = 1 := (BlockDat.lf_v_proj h).1.1
  have hΨ : (B.vPr ℓ).map v.embedding * (B.vE ℓ).map v.embedding = 1 := by
    rw [← Matrix.map_mul, hvv, map_one']
  have hΦ : ∀ i, (B.vE ℓ).map v.embedding * (tV B ℓ i).map v.embedding =
      (B.opMat i).map v.embedding * (B.vE ℓ).map v.embedding := fun i => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  have hmem : ∀ {S : Pl0 → K[X]} {z : Fin (B.dZ ℓ Z) → K}, z ∈ B.part ℓ Z S →
      (fun a => v.embedding ((B.zE ℓ Z *ᵥ z) a)) ∈ Col.eigSum (linF fun i => (tV B ℓ i).map v.embedding)
        (fun w => ∃ x, B.HasRes S x ∧ w = fun i => v.embedding (x i)) := by
    intro S z hz
    have h0 : B.S.basis.equivFun.symm (B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z)) ∈ Col.eigSum B.op (B.HasRes S) := by
      have := hz
      rw [BlockDat.part, Submodule.mem_comap, BlockDat.mem_goodPart_iff] at this
      exact this
    have h1 : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ Col.eigSum (fun i => Matrix.toLin' (B.opMat i)) (B.HasRes S) := by
      have := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) B.op
        (fun i => Matrix.toLin' (B.opMat i)) (fun i f => by rw [Matrix.toLin'_apply]; exact equivFun_op i f) _ h0
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    have h2 := emb_mem_eigSum v.embedding B.opMat (B.HasRes S) h1
    refine mem_eigSum_of_emb _ _ ((B.vE ℓ).map v.embedding) ((B.vPr ℓ).map v.embedding) hΨ hΦ hc hs hcf _ ?_
    rw [← emb_mulVec]
    exact h2
  have hPN : ∀ i, (B.Pq ℓ Z).map v.embedding * (tV B ℓ i).map v.embedding =
      (B.Pq ℓ Z * tV B ℓ i * B.zE ℓ Z).map v.embedding * (B.Pq ℓ Z).map v.embedding := fun i => by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map v.embedding) (Pq_tV h hH hZ i)
  have hCC : ∀ w, (fun w => ∃ x, B.HasRes Sg' x ∧ w = fun i => v.embedding (x i)) w →
      ¬ (fun w => ∃ x, B.HasRes Sg x ∧ w = fun i => v.embedding (x i)) w := by
    rintro w ⟨x', hx', rfl⟩ ⟨x, hx, e⟩
    have : x' = x := funext fun i => v.embedding.injective (by simpa using congrFun e i)
    subst this
    exact hSS x' hx' hx
  have key := cx_quot_orth (fun i => (tV B ℓ i).map v.embedding) ((B.HV ℓ).map v.embedding) hA
    (adjC h hH v.embedding) ((B.Pq ℓ Z).map v.embedding) _ hPN hR hc hs hCC (hmem hx) (hmem hy)
  have ex : ∀ z : Fin (B.dZ ℓ Z) → K,
      (B.Pq ℓ Z).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ z) a)) = fun a => v.embedding (z a) := by
    intro z
    rw [← emb_mulVec, Matrix.mulVec_mulVec, hpq, Matrix.one_mulVec]
  rw [ex, ex] at key
  rw [Formalism.L2.DIV.majAt_eq, hmet]
  exact key

end OrthogonalPartDecomposition

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)
variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem partsOrth_at {s : ℕ} (hOk : A.fam.Ok s) (hH : HeckeRatR A) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A.fam.base.Ix) (hpq : p ≠ q)
    (x : Fin ((A.fam.side P ψ X.zs).dQ A.fam.μ0) → K) (hx : x ∈ (A.fam.side P ψ X.zs).Qp A.fam.μ0 p)
    (y : Fin ((A.fam.side P ψ X.zs).dQ A.fam.μ0) → K) (hy : y ∈ (A.fam.side P ψ X.zs).Qp A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A.fam.side P ψ X.zs).XQ A.fam.μ0) v x y = 0 := by
  have hok := hOk.what₂ A.fam.μ0
  have hZ : ∀ i, X.Z A.fam.μ0 ≤ (X.Z A.fam.μ0).comap ((A.fam.R A.fam.μ0).op i) := fun i =>
    Submodule.map_le_iff_le_comap.1 (hst.1 A.fam.μ0 (Sum.inl i))
  have hmemR : ∀ r : A.fam.base.Ix, r.1 ∈ (A.fam.R A.fam.μ0).resSet A.fam.X := fun r =>
    ((A.fam.R A.fam.μ0).mem_ixFin hok.comm _ _).1 r.2
  have hSS : ∀ z, (A.fam.R A.fam.μ0).HasRes q.1 z → ¬ (A.fam.R A.fam.μ0).HasRes p.1 z := by
    intro z hq hp
    exact hpq (Subtype.ext (OrthogonalPartDecomposition.res_eq (hmemR p) (hmemR q) hp hq))
  exact OrthogonalPartDecomposition.part_orth (B := A.fam.R A.fam.μ0) (ℓ := A.fam.lvl P ψ) (Z := X.Z A.fam.μ0)
    ⟨hOk.conj, hOk.irr, hok⟩ hH hZ v hSS hx hy

theorem cutPartsOrth : CutPartsOrth A X P0 ψ0 P1 ψ1 Dc Sp Zsc := by
  intro s hOk hH hst b
  cases b
  · exact fun v _ p q hpq x hx y hy => partsOrth_at A X hOk hH hst P0 ψ0 v p q hpq x hx y hy
  · exact fun v _ p q hpq x hx y hy => partsOrth_at A X hOk hH hst P1 ψ1 v p q hpq x hx y hy

end Main

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) where
  A : FamIn K G Pl0 T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)
  Zsc : DefSub A.fam.amb → IndefScale A.fam.base
  X : CxData A.fam.amb
  gE : Representation ℂ G X.EE

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

abbrev cr : Crd I.A.fam.amb (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A.fam.amb (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A.fam.base.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A.fam.base.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A.fam.base.Tup) :
    Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A.fam.base.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))

open Classical in

def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

def eMat {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  (Formalism.IndefR.TransferLatticeStatement.charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, Formalism.IndefR.TransferLatticeStatement.charOf τ x⁻¹ • I.ρf x

abbrev LA {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : LevelAmb K (I.Sb false).D (I.Sb true).D where
  Dg := I.Sg.D
  Xg := I.Sg.XE
  Rg := I.Sg.RR
  ep0 := I.epM I.P0 I.ψ0
  ep1 := I.epM I.P1 I.ψ1
  S := S
  fS := inferInstance
  es s := I.eMat (τ s)
  nS s := Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨I.P1, I.ψ1⟩
  nbar := nbar
  G := Fintype.card G
  h0 := Nat.card I.P0
  h1 := Nat.card I.P1
  ι0 := I.Jm false
  ι1 := I.Jm true

structure Hyp (s : ℕ) : Prop where
  ok : I.A.fam.Ok s
  sep : I.A.fam.TypesSep
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A.side I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A.side I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : GUnit I.A I.X I.gE
  gequiv : GEquiv I.A I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A.fam.base.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A.fam.base.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PRange : Prop :=
  ∀ s, I.Hyp s → ∀ b, LinearMap.range (I.Jm b).mulVecLin = LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

def PLat : Prop := ∀ s, I.Hyp s → Submodule.IsLattice K I.Sg.RR

def PGLat : Prop := ∀ s, I.Hyp s → ∀ (g : G), ∀ x ∈ I.Sg.RR, I.ρf g *ᵥ x ∈ I.Sg.RR

def PSand : Prop :=
  ∀ s, I.Hyp s → ∀ b,
    (∀ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x ∈ I.Sg.RR) ∧
    ∀ y ∈ I.Sg.RR, y ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin →
      ∃ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x = ((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • y

def PGood {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) : Prop :=
  ∀ s, I.Hyp s → Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ I.A.fam.X → ∑ t, I.eMat (τ t) = 1

end In

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

variable {D : D7}

abbrev sigE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sigE_sigE (a : D.host.E) : sigE D (sigE D a) = a := star_star a

theorem gram_herm (V : HSp D) (i j : Fin V.rank) : sigE D (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem cA_incA' (a : D.host.E) : cA D (incA D a) = incA D (sigE D a) := by
  simp [cA, incA, sigR, inclR]

theorem gramA_herm (V : HSp D) (i j : Fin V.rank) :
    cA D (V.gram.map (incA D) i j) = V.gram.map (incA D) j i := by
  simp only [Matrix.map_apply, cA_incA', gram_herm]

def mkGA (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) : GA D V :=
  let g : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨Matrix.nonsingInvUnit M hd, hM⟩
  g

theorem aniso_data (V : HSp D) (hn : 0 < V.rank) :
    ∃ (u : Fin V.rank → D.host.E) (ainv : D.host.E), ainv * hsq (sigE D) V.gram u = 1 ∧ sigE D ainv = ainv := by
  have : Nonempty (Fin V.rank) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := exists_aniso (sigE D) sigE_sigE V.gram (gram_herm V) (gram_det_ne V)
  refine ⟨u, (hsq (sigE D) V.gram u)⁻¹, inv_mul_cancel₀ hu, ?_⟩
  rw [map_inv₀, sigma_hsq (sigE D) sigE_sigE V.gram (gram_herm V) u]

theorem exists_GA_det (V : HSp D) (hn : 0 < V.rank) (x : AE D) (hx : cA D x * x = 1) (hxu : IsUnit x) :
    ∃ (R : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (g : GA D V), mt V g = 1 + (x - 1) • R ∧ (mt V g).det = x := by
  obtain ⟨u, ainv, ha, hainv⟩ := aniso_data V hn
  have haA : incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
    rw [← hsq_map (incA D) (sigE D) (cA D) (fun a => (cA_incA' a).symm), ← map_mul, ha, map_one]
  have hainvA : cA D (incA D ainv) = incA D ainv := by rw [cA_incA', hainv]
  set R := proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)
  have hM := proj_unitary (cA D) cA_cA (V.gram.map (incA D)) (gramA_herm V) (fun i => incA D (u i))
    (incA D ainv) haA hainvA x hx
  have hdet := det_proj' (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv) haA x
  exact ⟨R, mkGA V _ hM (by rw [hdet]; exact hxu), rfl, hdet⟩

theorem splitDet : SplitDetP := by
  intro D V hn e he x hx hsupp
  obtain ⟨R, g, hg, hdet⟩ := exists_GA_det V hn (x : AE D) (by rw [mul_comm]; exact hx) x.isUnit
  refine ⟨g, ?_, ?_, hdet⟩
  · intro i j
    rw [hg, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    unfold SuppAtU at hsupp
    rw [hsupp]
  · have hxi : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := x.mul_inv
    set xi : AE D := ((x⁻¹ : (AE D)ˣ) : AE D) with hxi_def
    set x0 : AE D := (x : AE D) with hx0
    have p1 : (e * x0 + (1 - e)) * (e * xi + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    have p2 : (e * xi + (1 - e)) * (e * x0 + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    obtain ⟨y, hy⟩ : ∃ y : (AE D)ˣ, (y : AE D) = e * x0 + (1 - e) := ⟨⟨_, _, p1, p2⟩, rfl⟩
    refine ⟨y, ?_⟩
    unfold IsDetAt
    rw [hy, hdet]

end Formalism.IndefR.flipTwoThree

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FockModel2
section
noncomputable section

open Matrix

namespace Formalism.IndefR.FockModel₂

abbrev KVar (p q n : ℕ) : Type := (Fin p ⊕ Fin q) × Fin n

variable {p q n : ℕ}

def kvSubst (k₁ : Matrix (Fin p) (Fin p) ℂ) (k₂ : Matrix (Fin q) (Fin q) ℂ) (h : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (KVar p q n) ℂ →ₐ[ℂ] MvPolynomial (KVar p q n) ℂ :=
  MvPolynomial.bind₁ fun x => match x with
    | (Sum.inl a, c) => ∑ c', ∑ a', MvPolynomial.C (h⁻¹ c c') * MvPolynomial.X (Sum.inl a', c') * MvPolynomial.C (k₁ a' a)
    | (Sum.inr b, c) => ∑ c', ∑ b', MvPolynomial.C (hᵀ c c') * MvPolynomial.X (Sum.inr b', c') *
        MvPolynomial.C (starRingEnd ℂ (k₂ b' b))

def kvLap (a : Fin p) (b : Fin q) (P : MvPolynomial (KVar p q n) ℂ) : MvPolynomial (KVar p q n) ℂ :=
  ∑ c, MvPolynomial.pderiv (Sum.inl a, c) (MvPolynomial.pderiv (Sum.inr b, c) P)

def IsKHarm (P : MvPolynomial (KVar p q n) ℂ) : Prop := ∀ a b, kvLap a b P = 0

def IsUpperUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLowerUni {k : ℕ} (u : Matrix (Fin k) (Fin k) ℂ) : Prop := IsUpperUni uᵀ

def IsKVHW (μ₁ : Fin p → ℤ) (μ₂ : Fin q → ℤ) (ν : Fin n → ℤ) (P : MvPolynomial (KVar p q n) ℂ) : Prop :=
  (∀ u₁ u₂ u, IsUpperUni u₁ → IsUpperUni u₂ → IsLowerUni u → kvSubst u₁ u₂ u P = P) ∧
  ∀ (t₁ : Fin p → ℂ) (t₂ : Fin q → ℂ) (t : Fin n → ℂ), (∀ i, ‖t₁ i‖ = 1) → (∀ i, ‖t₂ i‖ = 1) → (∀ i, ‖t i‖ = 1) →
    kvSubst (Matrix.diagonal t₁) (Matrix.diagonal t₂) (Matrix.diagonal t) P =
      ((∏ i, t₁ i ^ μ₁ i) * (∏ i, t₂ i ^ μ₂ i) * ∏ i, t i ^ ν i) • P

def kvVar (i c : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  if hc : c < n then
    (if hi : i < p then MvPolynomial.X (Sum.inl ⟨i, hi⟩, ⟨c, hc⟩)
     else if hi' : i - p < q then MvPolynomial.X (Sum.inr ⟨i - p, hi'⟩, ⟨c, hc⟩) else 0)
  else 0

def kvMinorPlus (k : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (Matrix.of fun α β : Fin k => (kvVar (p := p) (q := q) (n := n) β α)).det

def kvMinorMinus (k : ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (Matrix.of fun α β : Fin k => (kvVar (p := p) (q := q) (n := n) (p + β) (n - k + α))).det

def kvDelta (ap am : ℕ → ℕ) : MvPolynomial (KVar p q n) ℂ :=
  (∏ i ∈ Finset.range p, kvMinorPlus (p := p) (q := q) (n := n) (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
    ∏ i ∈ Finset.range q, kvMinorMinus (p := p) (q := q) (n := n) (i + 1) ^ (am i - if i + 1 < q then am (i + 1) else 0)

def KashiwaraVergne : Prop :=
  ∀ p q n : ℕ,
    (∀ (k₁ : Matrix (Fin p) (Fin p) ℂ) (k₂ : Matrix (Fin q) (Fin q) ℂ) (h : Matrix (Fin n) (Fin n) ℂ),
      k₁ ∈ Matrix.unitaryGroup (Fin p) ℂ → k₂ ∈ Matrix.unitaryGroup (Fin q) ℂ → h ∈ Matrix.unitaryGroup (Fin n) ℂ →
      ∀ P : MvPolynomial (KVar p q n) ℂ, IsKHarm P → IsKHarm (kvSubst k₁ k₂ h P)) ∧
    (∀ μ₁ μ₂ ν (P Q : MvPolynomial (KVar p q n) ℂ), IsKHarm P → IsKHarm Q → IsKVHW μ₁ μ₂ ν P → IsKVHW μ₁ μ₂ ν Q →
      P ≠ 0 → ∃ c : ℂ, Q = c • P) ∧
    (∀ μ₁ μ₂ ν (P : MvPolynomial (KVar p q n) ℂ), IsKHarm P → IsKVHW μ₁ μ₂ ν P →
      ∃ (ap am : ℕ → ℕ) (c : ℂ), P = c • kvDelta (p := p) (q := q) (n := n) ap am)

section Fock

open Formalism.BasicNotions Formalism.IndefR.Datum

variable {D : Formalism.BasicNotions.D7} {m n : ℕ}

def lapF (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) (a : Fin (p τ)) (b : Fin (m - p τ)) (P : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial (FVar D m n) ℂ :=
  ∑ c : Fin n, if h : (a : ℕ) < m ∧ p τ + (b : ℕ) < m then
    MvPolynomial.pderiv (τ, ⟨a, h.1⟩, c) (MvPolynomial.pderiv (τ, ⟨p τ + b, h.2⟩, c) P) else 0

def IsKHarmF (p : D.what₂.Tau → ℕ) (P : MvPolynomial (FVar D m n) ℂ) : Prop := ∀ τ a b, lapF p τ a b P = 0

def IsHWF (p : D.what₂.Tau → ℕ) (μ₁ : ∀ τ, Fin (p τ) → ℤ) (μ₂ : ∀ τ, Fin (m - p τ) → ℤ) (ν : D.what₂.Tau → Fin n → ℤ)
    (P : MvPolynomial (FVar D m n) ℂ) : Prop :=
  (∀ (u₁ : complexSquareMatrixFamily D p) (u₂ : complementBlockMatrixFamily D m p) (u : HFam D n),
      (∀ τ, IsUpperUni (u₁ τ)) → (∀ τ, IsUpperUni (u₂ τ)) → (∀ τ, IsLowerUni (u τ)) →
      polySubst p u₁ u₂ u P = P) ∧
  ∀ (t₁ : ∀ τ, Fin (p τ) → ℂ) (t₂ : ∀ τ, Fin (m - p τ) → ℂ) (t : D.what₂.Tau → Fin n → ℂ),
    (∀ τ i, ‖t₁ τ i‖ = 1) → (∀ τ i, ‖t₂ τ i‖ = 1) → (∀ τ i, ‖t τ i‖ = 1) →
    polySubst p (fun τ => Matrix.diagonal (t₁ τ)) (fun τ => Matrix.diagonal (t₂ τ))
        (fun τ => Matrix.diagonal (t τ)) P =
      (∏ τ, ((∏ i, t₁ τ i ^ μ₁ τ i) * (∏ i, t₂ τ i ^ μ₂ τ i) * ∏ i, t τ i ^ ν τ i)) • P

def FockKV (D : Formalism.BasicNotions.D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) : Prop :=
  (∀ (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n),
      (∀ τ, k₁ τ ∈ Matrix.unitaryGroup (Fin (p τ)) ℂ) → (∀ τ, k₂ τ ∈ Matrix.unitaryGroup (Fin (m - p τ)) ℂ) →
      (∀ τ, h τ ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ P : MvPolynomial (FVar D m n) ℂ, IsKHarmF p P → IsKHarmF p (polySubst p k₁ k₂ h P)) ∧
  (∀ μ₁ μ₂ ν (P Q : MvPolynomial (FVar D m n) ℂ), IsKHarmF p P → IsKHarmF p Q → IsHWF p μ₁ μ₂ ν P →
      IsHWF p μ₁ μ₂ ν Q → P ≠ 0 → ∃ c : ℂ, Q = c • P) ∧
  (∀ μ₁ μ₂ ν (P : MvPolynomial (FVar D m n) ℂ), IsKHarmF p P → IsHWF p μ₁ μ₂ ν P →
      ∃ (ap am : D.what₂.Tau → ℕ → ℕ) (c : ℂ), P = c • delta p (fun τ => m - p τ) ap am)

def StepFockKV (D : Formalism.BasicNotions.D7) : Prop := KashiwaraVergne → ∀ (m n : ℕ) (p : D.what₂.Tau → ℕ), (∀ τ, p τ ≤ m) → FockKV D m n p

end Fock

end Formalism.IndefR.FockModel₂

end
end

