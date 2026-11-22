import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0366
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import GroundTheory.PAdicHodge.AInfGalois
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0005
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.ProjectionSandwichLength

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem tensorSp_levi {n : Fin 2 → ℕ} (h : ∑ i, n i = n 0 + n 1) (W₁ : Submodule ℂ (Sm E (n 0)))
    (W₂ : Submodule ℂ (Sm E (n 1))) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) :
    (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp (blkV W₁ W₂) := by
  have := tensorSp_of_tens2 W₁ W₂ hψ
  convert this using 2 with m
  rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]

theorem capR_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₁ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capR (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 0 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
    funext p q
    rw [CapFactor.std_zero, CapFactor.std_zero]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem capS_lev {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M : Multiset ℂ) (hM : HasInfCharGL W₂ τ M) (w : ℂ) (ψ : Sm E (n 0 + n 1))
    (hψ : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂) (p : GA E (n 0) × GA E (n 1)) :
    (capS (n 0) (n 1) τ w ψ).1 (lev (Ad E) (n 0) (n 1) p) = (M.map (w + ·)).prod * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  have key := GlobalTheory.NormIndCap.qdet_block_levi n h (blkV W₁ W₂) τ 1 M hM w ψ (tensorSp_levi h W₁ W₂ ψ hψ)
    (CapFactor.levPair p)
  have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
      fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
    funext p q
    rw [CapFactor.std_one, CapFactor.std_one]
  rw [e1, ← CapFactor.lev_eq_leviEmb n h] at key
  exact key

theorem casimir_on_parabolic_induction {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) (τ : E →+* ℂ)
    (M₁ M₂ : Multiset ℂ) (h₁ : HasInfCharGL W₁ τ M₁) (h₂ : HasInfCharGL W₂ τ M₂) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : MemInd2 W₁ W₂ F) :
    cap τ u F = ((M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod) • F := by
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  set c := (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod * (M₂.map (u + (n 0 : ℂ) / 2 + ·)).prod with hc
  have hlev : ∀ ψ : Sm E (n 0 + n 1), (∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g, ψ.1 (unip x * g) = ψ.1 g) →
      (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ → ∀ p,
      (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) p) = c * ψ.1 (lev (Ad E) (n 0) (n 1) p) := by
    intro ψ hψ hT p
    rw [CapFactor.cap_levi E (n 0) (n 1) τ u ψ hψ p]
    have hT' : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := by
      have e : (fun p => (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) ψ).1 (lev (Ad E) (n 0) (n 1) p)) =
          (M₁.map (u - (n 1 : ℂ) / 2 + ·)).prod • (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) :=
        funext fun p => capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p
      rw [e]
      exact Submodule.smul_mem _ _ hT
    rw [capS_lev W₁ W₂ τ M₂ h₂ _ _ hT' p, capR_lev W₁ W₂ τ M₁ h₁ _ ψ hT p, hc]
    ring
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h x
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  have hx : leviEmb (Ad E) (stdBlocks n h) m = lev (Ad E) (n 0) (n 1) (m 0, m 1) := by
    rw [CapFactor.lev_eq_leviEmb n h, levPair_eta]
  rw [hx]
  set y := infGL E (n 0 + n 1) (Unitary.toUnits k) * finGL E (n 0 + n 1) g
  have hcomm : Commute (cap τ u) (rt E (n 0 + n 1) y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E _ τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E (n 0 + n 1) y F
  have hψ : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) g', ψ.1 (unip x * g') = ψ.1 g' := fun x g' => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hF.1 x _
  have hψT : (fun p => ψ.1 (lev (Ad E) (n 0) (n 1) p)) ∈ tens2 W₁ W₂ := hF.2 k g
  have h3 := hlev ψ hψ hψT (m 0, m 1)
  have h4 : (cap τ u ψ).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1)) =
      (cap τ u F).1 (lev (Ad E) (n 0) (n 1) (m 0, m 1) * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  have hcapInv := (CapStable.capStable E (n 0) (n 1) τ u F).2 hF.1
  rw [mul_assoc, hcapInv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hF.1]

end PositivityTheory.Rg.Rs.PInfInd2A

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapB
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

namespace B

variable {R : Type} [CommRing R]

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  have := k.isLt
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dif_neg (fun h => by have := h.2; simp only [Fin.val_castAdd] at this; omega), add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dif_neg (fun h => by have := h.1; simp only [Fin.val_natAdd] at this; omega), add_zero]

end B

open B

theorem unip_zero {R : Type} [CommRing R] {a r : ℕ} : unip (0 : BlockIx a r → R) = 1 := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_zero

theorem unip_lev_ll {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i : Fin s) (j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have h : ∀ x : Fin r, Fin.natAdd r i ≠ Fin.castAdd s x := fun x h => by
    have := congrArg Fin.val h
    have := x.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at *
    omega
  simp [unip_row, lev_nc, lev_cc, Matrix.one_apply, h]

theorem unip_lev_cc {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) =
      (m.1 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_col, lev_nc, lev_cc, Matrix.one_apply]

theorem unip_lev_nn {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin s) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) =
      (m.2 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_row, lev_cn, lev_nn, Matrix.one_apply]

theorem lev_mul_unip {R : Type} [CommRing R] (m : GL (Fin r) R × GL (Fin s) R) (u : BlockIx (r + s) r → R) :
    ∃ v : BlockIx (r + s) r → R, lev R r s m * unip u = unip v * lev R r s m := by
  have h1 := GlobalTheory.CompanionTheory.CTFin.blockDiag_lev (R := R) m
  have h2 : GlobalTheory.CompanionTheory.CTFin.BlockDiag r ((lev R r s m)⁻¹).val := by
    rw [← map_inv]; exact GlobalTheory.CompanionTheory.CTFin.blockDiag_lev _
  refine ⟨(GlobalTheory.CompanionTheory.CTFin.conjE (lev R r s m) h1 h2).symm u, ?_⟩
  rw [GlobalTheory.CompanionTheory.CTFin.unip_mul_eq _ h1 h2, AddEquiv.apply_symm_apply]

theorem cf_mul (a : ℕ) (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) : cf a k g * cf a k' g' = cf a (k * k') (g * g') := by
  refine ga_ext ?_ ?_ <;> simp [cf]

theorem exists_decomp (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)), x = unip u * lev (Ad E) r s m * cf (r + s) k g := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨y, m, t, k, l, -, -, rfl⟩ := hT x
  refine ⟨y, m, k, t * l, ?_⟩
  rw [cf, map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

theorem levi_cf {u : BlockIx (r + s) r → Ad E} {m : GA E r × GA E s} {k : Kinf E (r + s)} {g : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m = cf (r + s) k g) :
    ∃ (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (g₂ : GL (Fin s) (Af E)), m = (cf r k₁ g₁, cf s k₂ g₂) := by
  have h1 := congrArg (Matrix.GeneralLinearGroup.map (pInf E)) h
  rw [map_mul, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_lev, cf, map_mul, pInf_infGL, pInf_finGL, mul_one] at h1
  set y₁ := Matrix.GeneralLinearGroup.map (pInf E) m.1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.map (pInf E) m.2 with hy₂
  have hv : ((Unitary.toUnits k : GL (Fin (r + s)) (Cinf E)) : Matrix _ _ _) = k.1 := rfl
  have hll : ∀ i j, k.1 (Fin.natAdd r i) (Fin.castAdd s j) = 0 := fun i j => by rw [← hv, ← h1, unip_lev_ll]
  have hcc : ∀ i j, k.1 (Fin.castAdd s i) (Fin.castAdd s j) = y₁.val i j := fun i j => by rw [← hv, ← h1, unip_lev_cc]
  have hnn : ∀ i j, k.1 (Fin.natAdd r i) (Fin.natAdd r j) = y₂.val i j := fun i j => by rw [← hv, ← h1, unip_lev_nn]
  have u₁ : y₁.val ∈ Matrix.unitaryGroup (Fin r) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) (Fin.castAdd s i)) (Fin.castAdd s j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hcc, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply,
      Fin.castAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  have u₂ : y₂.val ∈ Matrix.unitaryGroup (Fin s) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 k.2) (Fin.natAdd r i)) (Fin.natAdd r j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hnn, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply,
      Fin.natAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  refine ⟨⟨_, u₁⟩, Matrix.GeneralLinearGroup.map (pFin E) m.1, ⟨_, u₂⟩, Matrix.GeneralLinearGroup.map (pFin E) m.2,
    Prod.ext ?_ ?_⟩
  · exact (infGL_mul_finGL m.1).symm.trans (congrArg (fun z => infGL E r z * _) (Units.ext rfl))
  · exact (infGL_mul_finGL m.2).symm.trans (congrArg (fun z => infGL E s z * _) (Units.ext rfl))

theorem lev_mul_infGL (m : GA E r × GA E s) (u : BlockIx (r + s) r → Cinf E) (b₁ : GL (Fin r) (Cinf E))
    (b₂ : GL (Fin s) (Cinf E)) (κ : Kinf E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * infGL E (r + s) (unip u * lev (Cinf E) r s (b₁, b₂) * Unitary.toUnits κ) =
      unip v * lev (Ad E) r s (m.1 * infGL E r b₁, m.2 * infGL E s b₂) * cf (r + s) κ 1 := by
  have e : infGL E (r + s) (unip u) = unip fun p => sInf E (u p) := by
    refine ga_ext ?_ ?_
    · rw [pInf_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      congr 1
      funext p
      exact ((infEq E).symm_apply_apply _).symm
    · rw [pFin_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      exact unip_zero.symm
  obtain ⟨v, hv⟩ := lev_mul_unip m fun p => sInf E (u p)
  refine ⟨v, ?_⟩
  rw [map_mul, map_mul, e, ← GlobalTheory.CompanionTheory.CTFin.Slice1.lev_infGL, ← mul_assoc, ← mul_assoc, hv, cf, map_one, mul_one, mul_assoc (unip v),
    ← map_mul]
  rfl

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.SpehInfChar

namespace PositivityTheory.Rg.Rs

namespace InfinitesimalCharacterAscent

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem prod_neg (d : ℕ) (g : ℂ → ℂ) :
    ∏ i : Fin d, g (-(spehExp d i : ℂ)) = ∏ i : Fin d, g (spehExp d i : ℂ) := by
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end InfinitesimalCharacterAscent

open InfinitesimalCharacterAscent in
theorem infAsc_holds : InfAsc := by
  intro E _ _ _ N a d V π hV hemb τ m hm
  obtain ⟨hs, ν, hν, f, hfm, hfi, hfe⟩ := hemb
  have hm0 : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  set m₀ := (CG.mk π).infChar τ with hm₀
  refine ⟨m₀, hm0, GlobalTheory.BcSpehProof.hasInfCharGL_unique hV.ne_bot hm ⟨?_, fun u φ hφ => ?_⟩⟩
  · rw [← hs, Multiset.card_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Multiset.card_map, hm₀, CG.card_infChar]
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  have hIV : ∀ X, ∀ φ ∈ V, lie E N X φ ∈ V := fun X φ hφ => hV.stable (.lie X) φ hφ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m₀.map (· + expo (ν i) τ))
    (fun i => hm0.twist (ν i)) u (f φ) (hfm φ hφ)
  have e1 : f (cap τ u φ) = cap τ u (f φ) := cap_comm_quot hIV f hfe τ u φ hφ
  set Q := ((∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))).map (u + ·)).prod with hQ
  have hQ' : (∏ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
      u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod) = Q := by
    rw [hQ, prod_map_finset_sum]
    have e : ∀ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
        u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod =
        (m₀.map fun x => u + x + -(spehExp d i : ℂ)).prod := fun i => by
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]
      rw [hexpo i, hmod i]
      push_cast
      ring
    rw [Finset.prod_congr rfl fun i _ => e i, prod_neg d (fun t => (m₀.map fun x => u + x + t).prod)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]
    ring
  have hmem : cap τ u φ - Q • φ ∈ V := by
    rw [hm.2 u φ hφ]
    exact V.sub_mem (V.smul_mem _ hφ) (V.smul_mem _ hφ)
  have h0 : f (cap τ u φ - Q • φ) = 0 := by
    rw [map_sub, e1, hc, map_smul, hQ']
    exact sub_self _
  exact sub_eq_zero.1 (hfi _ hmem h0)

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesB
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in
theorem absC_mul (s t : ℂ) : Model.absC E s * Model.absC E t = Model.absC E (s + t) := by
  apply Subtype.ext
  ext x
  change Complex.exp (s * _) * Complex.exp (t * _) = Complex.exp ((s + t) * _)
  rw [← Complex.exp_add, add_mul]

omit [IsTotallyComplex E] in
theorem isAbsPow_absC (x : ℝ) : (Model.absC E (x : ℂ)).IsAbsPow x :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow x

omit [IsTotallyComplex E] in
theorem eq_absC {ν : HChar E} {x : ℝ} (h : ν.IsAbsPow x) : ν = Model.absC E (x : ℂ) :=
  PositivityTheory.RSHS.ProjectionSandwichLength.eq_of_isAbsPow h (isAbsPow_absC x)

omit [IsTotallyComplex E] in
theorem chiDet_leviEmb {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (χ : HChar E) (m : ∀ i, GA E (n i)) :
    ((chiDet N χ (leviEmb (Ad E) (stdBlocks n h) m) : ℂˣ) : ℂ) = ∏ i, ((chiDet (n i) χ (m i) : ℂˣ) : ℂ) := by
  simp only [chiDet, MonoidHom.comp_apply, det_leviEmb, map_prod, Units.coe_prod]

theorem tensorForms_mulChi {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i)) (χ : HChar E)
    {G : (∀ i, GA E (n i)) → ℂ} (hG : G ∈ tensorForms π) :
    (fun m => G m * ∏ i, ((chiDet (n i) χ (m i) : ℂˣ) : ℂ)) ∈ tensorForms (fun i => (π i).twist χ) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine Submodule.subset_span ⟨fun i => ⟨mulChi (n i) χ (φ i).1, ⟨(φ i).1, (φ i).2, rfl⟩⟩, funext fun m => ?_⟩
    simp only [mulChi_apply, Finset.prod_mul_distrib]
  | zero =>
    convert zero_mem (tensorForms fun i => (π i).twist χ) using 1
    funext m
    simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [mul_assoc]

theorem tensorForms_append {d₁ d₂ a : ℕ} (π : Fin (d₁ + d₂) → CuspSub E a) {G₁ : (Fin d₁ → GA E a) → ℂ}
    {G₂ : (Fin d₂ → GA E a) → ℂ} (h₁ : G₁ ∈ tensorForms (n := fun _ => a) (fun b => π (Fin.castAdd d₂ b)))
    (h₂ : G₂ ∈ tensorForms (n := fun _ => a) (fun b => π (Fin.natAdd d₁ b))) :
    (fun m : Fin (d₁ + d₂) → GA E a => G₁ (fun b => m (Fin.castAdd d₂ b)) * G₂ (fun b => m (Fin.natAdd d₁ b))) ∈
      tensorForms (n := fun _ => a) π := by
  induction h₁ using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, rfl⟩ := hF
    induction h₂ using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨φ₂, rfl⟩ := hF
      refine Submodule.subset_span ⟨Fin.addCases (motive := fun i => ↥(π i).V) φ₁ φ₂, funext fun m => ?_⟩
      simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
    | zero =>
      convert zero_mem (tensorForms (n := fun _ => a) π) using 1
      funext m
      simp
    | add F G _ _ hF hG =>
      convert add_mem hF hG using 1
      funext m
      simp [mul_add]
    | smul c F _ hF =>
      convert Submodule.smul_mem _ c hF using 1
      funext m
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  | zero =>
    convert zero_mem (tensorForms (n := fun _ => a) π) using 1
    funext m
    simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end PositivityTheory.Rg.Rs.InductionInStages

end
end

