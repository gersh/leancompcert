import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572094763901853, 360572099142529225⟩, ⟨285193538376938702, 285273800977665772⟩, true⟩

def state01 : KState := ⟨⟨360663514811594845, 360663519193583232⟩, ⟨(-2192763191548851800), (-2192682837847600576)⟩, true⟩

def words00 : List Nat := [360582625867242487, 360582626955938534, 360582629403536400, 360582631851030154, 360582633124081510, 360582633124437782, 360582634319862890, 360582635597100170, 360582638232762825, 360582641216457800]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360649609583458023, 360649613968845119⟩, ⟨(-1815886611333139419), (-1815806165476047899)⟩, true⟩

def words01 : List Nat := [360582643150109495, 360582645083651967, 360582647579953377, 360582650758998985, 360582652611385246, 360582654463689918, 360582655405566869, 360582656994608731, 360582659463812251, 360582661932951309]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360657552887017222, 360657557275758816⟩, ⟨(-2031449473262813297), (-2031368936414582849)⟩, true⟩

def words02 : List Nat := [360582665159260551, 360582667520749291, 360582669198462400, 360582670876090656, 360582671550854204, 360582673291789407, 360582676389041504, 360582679486133340, 360582681899923051, 360582684660064055]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360644319646446751, 360644324038560367⟩, ⟨(-1672377124893568144), (-1672296496546169240)⟩, true⟩

def words03 : List Nat := [360582687808814045, 360582690957443330, 360582694943188930, 360582697577395017, 360582698999685241, 360582700421895183, 360582702049582869, 360582704357859342, 360582706628590649, 360582708899230712]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360651833720607677, 360651838116119085⟩, ⟨(-1876578543668616918), (-1876497823088604598)⟩, true⟩

def words04 : List Nat := [360582710444437227, 360582711271121712, 360582713452362672, 360582715633552856, 360582717193552604, 360582718838739917, 360582719801779048, 360582720764788462, 360582722173793540, 360582724719813660]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271A
