import Clear.ReasoningPrinciple

import generated.L2AssetRouter.L2AssetRouter.Common.block_6167488384460345248
import generated.L2AssetRouter.L2AssetRouter.Common.block_1305312945061517659
import generated.L2AssetRouter.L2AssetRouter.Common.block_1861012276691293798
import generated.L2AssetRouter.L2AssetRouter.abi_encode_bytes
import generated.L2AssetRouter.L2AssetRouter.Common.block_8303368798228693998
import generated.L2AssetRouter.L2AssetRouter.finalize_allocation
import generated.L2AssetRouter.L2AssetRouter.Common.block_164702752171606109
import generated.L2AssetRouter.L2AssetRouter.mcopy
import generated.L2AssetRouter.L2AssetRouter.Common.block_8767075098902109563
import generated.L2AssetRouter.L2AssetRouter.Common.block_5662293332900707030

import generated.L2AssetRouter.L2AssetRouter.fun_encodeTxDataHash_gen


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2AssetRouter.Common generated.L2AssetRouter L2AssetRouter

def A_fun_encodeTxDataHash (var_txDataHash : Identifier) (var_originalCaller var_assetId var__transferData_mpos : Literal) (s₀ s₉ : State) : Prop := fun_encodeTxDataHash_concrete_of_code.1 var_txDataHash var_originalCaller var_assetId var__transferData_mpos s₀ s₉

lemma fun_encodeTxDataHash_abs_of_concrete {s₀ s₉ : State} {var_txDataHash var_originalCaller var_assetId var__transferData_mpos} :
  Spec (fun_encodeTxDataHash_concrete_of_code.1 var_txDataHash var_originalCaller var_assetId var__transferData_mpos) s₀ s₉ →
  Spec (A_fun_encodeTxDataHash var_txDataHash var_originalCaller var_assetId var__transferData_mpos) s₀ s₉ := by
  intro h
  simpa [A_fun_encodeTxDataHash] using h

end

end generated.L2AssetRouter.L2AssetRouter
