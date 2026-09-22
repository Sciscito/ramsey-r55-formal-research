import LRATCatcher.Tests.R44Cover6ConditionedWitnesses
import LRATCatcher.Tests.R44Cover6Master7R34FgraveGowCore

/-!
  # Selected-core semantics for the F`GOW degree-seven branch

  This module checks only the 5,807 clauses retained by the tracked compact
  LRAT core.  Its compact payload contains one fifteen-bit orbit/lift witness
  for each of the 3,227 K7 clauses and 2,396 projected K6 clauses in core
  order.  No complete F7 stream and no assignment space is enumerated.
-/

namespace LRATCatcher.Tests.R44Cover6Master7R34FgraveGowSemantics

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44OrderTwelveRootSymmetry
open LRATCatcher.Tests.R44Cover6MotifBridge
open LRATCatcher.Tests.R44Cover6CubeBridge
open LRATCatcher.Tests.R44Cover6RepresentativeCubes
open LRATCatcher.Tests.R44Cover6S7Transport
open LRATCatcher.Tests.R44Cover6SemanticComposition
open LRATCatcher.Tests.R44Cover6ConditionedWitnesses
open LRATCatcher.Tests.R44Cover6DegreeSevenR34Normalization
open LRATCatcher.Tests.R44Cover6Master8IndexedSource
open LRATCatcher.Tests.R44Cover6Master7R34IndexedSource
open LRATCatcher.Tests.R44Cover6Master7R34FgraveGowCore

set_option maxRecDepth 100000

/-! ## Ordered taxonomy of the tracked core -/

def d7CoreArrayPosition (position : Fin 5807) :
    Fin fgraveGowCoreFinIndices.size :=
  ⟨position.val, by rw [fgraveGowCoreFinIndexCount]; exact position.isLt⟩

def d7CoreSourceIndex (position : Fin 5807) : Fin branchClauseCount :=
  fgraveGowCoreFinIndices[d7CoreArrayPosition position]

def d7SelectedCoreClause (position : Fin 5807) : CNF.Clause Nat :=
  (branchSource fgraveGowCatalogueIndex).clauseAt
    (d7CoreSourceIndex position)

def d7BaseCorePosition (position : Fin 168) : Fin 5807 :=
  ⟨position.val, by omega⟩

def d7RootFreeCorePosition (position : Fin 3227) : Fin 5807 :=
  ⟨168 + position.val, by omega⟩

def d7RootContainingCorePosition (position : Fin 2396) : Fin 5807 :=
  ⟨3395 + position.val, by omega⟩

def d7UnitCorePosition (position : Fin 16) : Fin 5807 :=
  ⟨5791 + position.val, by omega⟩

theorem d7BaseCoreSourceIndex_range (position : Fin 168) :
    (d7CoreSourceIndex (d7BaseCorePosition position)).val <
      d7BaseClauseCount := by
  native_decide +revert

theorem d7RootFreeCoreSourceIndex_range (position : Fin 3227) :
    d7BlockClauseStart ≤
        (d7CoreSourceIndex (d7RootFreeCorePosition position)).val ∧
      (d7CoreSourceIndex (d7RootFreeCorePosition position)).val <
        d7LocalClauseStart := by
  native_decide +revert

theorem d7RootContainingCoreSourceIndex_range (position : Fin 2396) :
    d7LocalClauseStart ≤
        (d7CoreSourceIndex (d7RootContainingCorePosition position)).val ∧
      (d7CoreSourceIndex (d7RootContainingCorePosition position)).val <
        f7ClauseCount := by
  native_decide +revert

theorem d7UnitCoreSourceIndex_range (position : Fin 16) :
    f7ClauseCount ≤
        (d7CoreSourceIndex (d7UnitCorePosition position)).val ∧
      (d7CoreSourceIndex (d7UnitCorePosition position)).val <
        branchClauseCount := by
  native_decide +revert

/-! ## Compact selected witness stream -/

/-- Concatenated fifteen-bit codes: 3,227 K7 orbit witnesses, followed by
2,396 canonical K6 full-lift witnesses. -/
def d7CoreWitnessChunks : Array String := #[
  "oDM0oxYxpJbUQQekALHfU6NlueA5pu_XhGSkArpuw57Lf4AzFS1ZxUekArpuw57Lf4A5puq5_pJ1ZhqJkA5LfO6dkuxYhqJkA5Lf4AbkuocvFSP3DOS5YpLfAArpuw5dGfO6dkuQJsVoFgRlSXYo2g6ErWvs972g0E5Wvm9_HTD6TJKxbhIT76DmSMGrmf6CtEvGG5mf0C7EvFgxrK91r2g6ErWvs972g0E5Wvm9_rKxbB9eLgBKK1cp2g6ErWvs972g0E5EvRYQlS76T8eMGrmf6CtEvGG5mf0Ct2g6CtEvKV0QnuGs7oewsptKJJRQMBcKXa-6rW91rJXYwU8eGBsQn-Gs-ZaAaqtY6aKXP3rJXY6KKtJ3T8e-GcKXa-6rWewsJXY6qptGB67oMBs7oa-6Lt915VaYw-XsRYQlSbJiGSEZeDSbJ4eY3qkgeDUAHKfbRiSaFys4JJyCSMB6Yoa-6rWewE9eUAS8eGBsQnUAKqWYws7oa-ERee6qptKJ37o-GcKXYwETK315QnMBs7oaA4LtyVqJXU-U8ee6SJKXYAmSMGrWv0E5Evxbp2g6C7mf0C7EvLgp2g6ErWvGG5mf0CF9eMG5WvD6TJKXYomf6CtEvGG5WvLgxmeMGrmf6C7WvzpUESlbJnZLd8KKO9_OY7UwCSkDjb4DJCHKfbxmJH7EjSZbRESILakuS57PoSKsPoYKkneq0NjXkCKDuk0_meSH6PoSKMaoYjfnef5LjXkCKDucS0PoYKMCamDacXq0t5ucSm4Q8JsPoYK6kXm17PoEJkne8JsPoYK6kXqCqbXCkn5uF2aos4q-llGq--KBhRzK-9RVKAqsPXnmLET2DdDTSeYVTsCs0PMqcrsq73IP08Z6ulZoVsAqcvWkCKNtfhh_KUcoFT2i3mKWfxKCPm9fCjWxrRSqcGP4qkVek7J_O-pU5n1pj_Knyg4krZQSTeeoCT0cAcCjYvNCMZY-OKs6YsBhRzKww-Ok7_oFTshJWTdWpIPB0aZsKs60PR1rnsxZozOAq-LkCxcZXH5zyS7p55L8i3mKCc2CTNUZ3LyhxcCjWZostdoFPk7pVsXdZMtZhxySkeoUTCc2CTifBNCdWB0EGZY1PiBColKs60PtdwvSk7hRTXdBOkS0l4kZhR0LIcoUTGuyKCSewcCHUB4S4AZosGqMpsUDyOkufJoKMeoUTs83hs4ZgHFLzYD5shpRTwgpITyhJ5f8dYqKIIccisUWUnCIMVnQ_-Ued15MQsUmMQqBcHowBMIoeK6-hW_suWWD6-nqBcHowBMIoW_cvWCxMRX674s3mIZUnCIMVnII6ytQBKxt6x6s3sFsYaMmXPtQ_ss3CIMVnII6SXCxMRX67yCeSK6kXkCKDucSGCam1d6ugDq5uYK6kXqCa6ueXKjXg1t5u8J6EukCKDuk0_meZ55a38J6EukCSie7iZZoYK6kX6YaWsGq6kXAApnsRdxvSlZozOw7JjXThpuWDagvNrZ2pKofJ4LCcY3LmhhnKlU3RaMApkX4qk3Wj9kXlBhpFPAApzOAqEuNrxT0LOcopK-fJ4LWf3UTDtBZaHUB4STUZrs4ApFPQssVsxojUKuf35LcfZDTmhBcCMApkXC8ZGPtdQPTAAJps-pE6keew4SjYfpR4gvrKRYQlS76T8eMGrmf6CtEvGG5mf0C7EvFgxrK31r2g6ErWvs972g0C7EvRYQlS91DKKMGrmf6CtEvGG5WvxbhITrcAKK6ErEv0E5EvD6D9e1cp2g6ErWvs97mfm9VtKD6TlS31r2g",
  "6ErWvs97mf0Cle4bUAmS4ALdYIFyXszcePYDUgDSXY2xXyYmFfu9TWsV1j9eDUgDS9YAmSrbpP43q-_Odau6YpaOGKZbJPKgcp0Pcsc1PcbY-OhdIHPEs-TKk7x6ngDKDu7pbnKifZ3LvWh5S683vSSAZ1PiBaZsq7ZWs083Ysk7pVsC7CTTzdAuNN-jsNroTST3e2FTcf3mKdY1UT9rhlDpYnIPs1dGP4qcRKGqMHPlhpVsAqkRTzdAuNndQ0Luf3NdGeY3LyhRWTGA3YsnygdNr-25LIcIETshZnKifhpRMA3bsE9xtmMeIabgcIjYqgBjeFdxTKd1LAg2FLevoAd9gyEbdviAVzKFdJAg2DNMvCHbtfiAFjelZAQTrZIuf2DNMvCHbtfyCdLvhdwTKj1DQTndgwSIHLuf2DdtfyCdLvndgwSIHLuf2DNMvCHbtfyCdLvHhB-KrZIAg2FLevcbYWsNhRPTQsccXk7h_K-fJWT0c2CTSeYVT9bfLC68pSXMqc1PSqcGP083Ys-9RBeEsU5kw7hRTnmzCeOc25LIcYnKnaP6SC8ZZsaDaos4q60PGqUzK-9xZNhmTfeThh_Kqw-KWndgUKroTSTcfxfC_WpYsNhRzKlZIDuQ_E1L7pLWTZUx_OD1D_O7JCKK1cJzXKZGYRdau6Y3YQiSgFqju_7xXsFHy6Y9YQGK1cBFS_7BBe95jnJlbBv4LYw_OWsMgsmeeeEWfJNTyhhPYwKCfeL5jb49YAjS7UApJMGT-OzGCHKfbRlSvXJlfq5lYsD1zCSlbJEfzuiAdRqknO_73PXOrctKyhpLTM5NfuwKaeu3viZHWsse3lvXoYcaoITGeY3LgcIB5acoAWy-KVVMlpAW6UJVVMlJTRM1qmR0UJBjWKLVVikr2i2h5PjQmLLtLvjku0UpagQf5agckbrjMWLOjKmL3k85sfmLvD9rcKLBjWKbAjwx3BlMWTKbQm5fmfkragQfbAjIvrqj2hr-iYDc2kE5k4iKlsIgqxpag6UpqjSWb2k85sfmPibmhcKLBjWKbAj6UpqjOvbrjMWDBuQmrfmPij4imRZBWsMLSlIabmjAkbaemMLujykrUReoLYi4kLnjA9cMriZ5URS1qsgmMbtjY14Zi4kLnj49M9n1oDaibxbBW2lLSlYoLYiIj5hjOab8nS1qsgmMLujykLSlOaz2x4kLnjc-kSlsM5sgykLCWIarnmOabmjA9EGkMpsIrRargYIjzGdEhL7ZkOiVq8hrPhao5DhKR51hkPrCYeLyUqOjb6ZXDoPhuLj7roRrShhZsMjyAXNjwOafjePDBvUNLzgHesMjygbqYCjrGdSP5xgcRL8m6qbPmI3M-nu66_nY1M4l7ocAlQvbYot1sWk0qL2jI3M-nu6MCmYubAlQvbYoQKsyu0qbPmI3s0Uo6MCmfE5DmKvbYoQKsWk0qLQmuFM4le1Ewnn1k4l024WkC3MQm62K-nYur4wAHtWk0qbPmI3s0UY1MBlQKEwnInnkjeRH-h-7rEj0rbQnxkciFkyiPbUA6Mn40sYdcx4BEJlsyhMuDiTnuBofo6-oujHV6OiVr_hSur5l48bYmilyAsqanZfM22ojD7cftWNbHWOmJZmu55amclaNdDhCUlI24XmmabafSgqeC1haJGSB42k46rJW4GsfiQkbdik6SytXjCTHzqycTpFZ4U84sXmMG6FluKc3vV7c4Ua2Kbk84sXmuv5doj2cakamJbk84sXmSG6Fl-v5do-KE3oaqb4U84sXmS7kDe-v5doDGM4v",
  "j2cLvp2cak84c3o-KUytaq5XmE4MLWM7cxmDFzevZnsFluKsdoAmbdf4GMxbM22eCHn-Uwk9c1UgqL1kyCricqErZfG2ANvzxbakGm5IbWrKkcawSXvO2cvWkanAncKsMdSgSNbC2MHGwEbfCN0CumZ_-ouaz9urXHVXvLssEjyu5PnNkZzhSuDlT9v3MnTH7BciVb3lrgaZk-_LLnZ5lKLXHt2l-VTNbBClvrkurXlYFMYmIrz6vTGycTwlXbUuqZeUa35NlKNFrfDCrBWjscQwnDEnwRHcbCe_b-lS5cbUWzp7lKx5AlArZhwyw9ofNI60xoqZnea3bPeZC7LovKc1oDONzVArp2xm8MTeswv4v8JFdofIUOUa04wjIFrhXCw5pmIwrpmc96Zoqz5LokIkDuFKMlmO66aUK0qCnIKcDnOK6LoUCtww0wbHlO66aUU6comeIsLoO6c2WIwrpmiLqaUQ0KYo26cRld8tLo9Kk2nf9ckmCw5pmWqppmQ04ZoSxLllkIMvwl9cHlO6MIlU6M3Wc9MlleIEXo2D7EhK0q1WwlbOiUHEeb7-rjjIwL3WQiKzcO8cLimdjSME17ls1-59u7-zDny_J3WQY57g4j44gmmbXo-iK3gI6wmlP-51WE0K3Wymr0nAHLBu5zbbU4v5Rei1zofENtXlHIUBoiqZQl60MRlczJfU215meE1jiejKk8wZI-cX-q3OeW1bheA5LgwZIs7l-qprEwsXTd1lUeuj5FiTkDEfueub0iOAcck-_b9cmbqyhMuDqsj0B7Oo_DLlyfb0m-_LLnX03YdF5tyhMuDiT95lguiVDbvuVD9VLsM_nqqrekgA-fuMur_hDl6QBPl6_htu3EjyfbKn0rTIt9FRhHjjJOGqtKQU-qJDWbCzcfbEc7WklbBkQyDFMzoEpVyXbqkr9arnPrhvuJ7Nok6sbyfyXDPsuWXnkOFDsb4nL9kQEMlloybcwX_cgEA5QrVpB7fEb7tjlYwLZlgGswj-rnPvPEMXXFn56WvDyutjaybf5GBfTybUILPiRLLZGZNGckXRVy-4AWOW4mRik5PjQmj4i0Upqjikr2iKm5fmE5cmhMWL3k85MxrufbUVIvrqjMWrnm2hLVl8hb3iQmD9rqxpmRIvrqjOvr2i2hb2k85smRikr2i2hL3k85sfmfkLxrhW5URS1KYiOabmjAkL9nGg6URYx5TlIaLgjOjrii4kLnj49-EvmRZBWY14Lk4kLnj49M9nXaLSlIaLgjOjb8nA9MKkeo5hjA-DGkIMbtjYoLYiOaLnj49EaiMg6hjEhjVqvI3DhiRjgHnZsjYWy6hjuLLzghZctYCjLLkQRjzqsgrpYajbfjONrSh21s0Uu6MCmYu55lKvLBlKKsyum9FDwt1M-nu6MCmKvLBlKKMZofHV_neu5Dm7ocAlKKMZoc7FEmyl40U624_nY1M4le1Ewnc7tEvn1-Em21s0U62KCme1MBlQK-Em62KCmYu5DmKvrka_jReuYu55lxgqEj8BshkxkcljxgqJnmAM6wxkcRB7ls2lBELddqy42fGR1_lWvL7cW6kguiVred6dL1fSur5l-mL9wewXKWwwXYmQra3oyCrrfQIcftmqbwgC243Uu55GmI26cfD76XRsqr_jE4sJWyCbJbFskpcUCLtf9yT8rC2K1k46rJWg2aMk4G-ztPixcTMGc3o6v5FluKMMv-1c4UMGs8l7D7Fl-v5do5Hd4Ua2q8librFl-KkLmP7cKWS7cCoZCtFluKsdoY8FHmj2Exm-KcLv",
  "g2qwm-KUMma2KZm46rJWAgazbyC5ybmCz9M-1oZfkanAwENb1UC2aKWAm5icclqvbQlavWaWhpcXkTWlaq52kE46icaCrvb6b9UlmnM1k02UNbaeL7cX5_ou1lshF74SnTszn_evG7kaz4NPBBETkTiVb3lSq5Mny4UtrMRXBmMubzheub3luVrMnAR9CwMur_hxgCxrYF6MnsA-vPti3xViq3dUK1rbmyxhBwS2ykniq3Pl-ubQlGvrPlY5M9lcxLfUW1bhwM5z4vvK-IoZI6jmEx5Oec1bVeSL7Nl2NVIvdK-sWoqJfUY5LdmE1DdoCL_IofIU6wKKNOva0y9WNooMCurfafJKkefoknGlc96ZoTHTutqzLlleIsLo9K-Xoc9MYoTHbklkIEDn0w5aUi96Lo9KkYof96wwcqJ3WUHMineIsLoL8EDnWqJ3WIKcDnOKMllUCl2nQ0qCnMxLind8NlleIckjWYrBuCwr1WAWZBgmmL3gyYnxmy_3pmU6cUesmrAgy567gaYX_V20q1WQ04QltkqMCiYbhmiqZeUAvLrkW15met7l4uhDcbU60sme-wbheE1bsEA55vkwsfieEJdbUcxbAeG5LBnj8t_w0tHgw8J7Alg3rrEUmbmEHwUtrMR9ur0nSeu9575lLs6Jnsf5bkqqDHm0rr_r_G_qtN6_CwGyCfuUnfpfPlcFjqqjJtcVr2l9575lq16_hhuJ_nU4MWo9-MLnX5lKLUz12fDl6QBPlc3l4Wj7VmfbFjA0ETHjjJOG8AKfUorn3kYXnpw9njaftCDWo0CKQb77_nOA5AxuyXbnk8YLzfSnDFMD7dFiasjQs4nLhmWEcrnQtyntY4-Msvngvu6sbFias5Hi4nL9kQEEnOFp-sbb7dqk22Lsj4XHhNoW1Eu78xitc0yEY3DAZTjfSEb9jReHLFZbY_fK_DbWSvol11kiCoHbnpt0L9jX4C0pXyjdkAnC0lt6cTRRcyZlhxK8mW0yD_bQs6q2Ye7xuQjgiX6lo_eLJckGpxZrhhL8gWGxD5cAt6k2oCqoLk8j6TiH2Pme4aBN-D8fzaaneAfDapXKIEjtujdf1vzsqGxTTd2164q2Ye7iX6lo_ej-sgiB-WXRs5QUViUTj2H545cAt6k2Akg5f5kiCoHbnaCU-6eAnkijX4C0pXKIElzCD8kAfuoc1uzsWoSzWRRcyZlhxK8mW0yDpsWMGxuQjgiX-7jrtMbTn7q5QrhhL8gWGxD5cAt61vAkgcX-D8mbbHEfzS-6eAnkiW1OEajtujdf1fuoaV464WlP7NhLbDquLESpj2H54vsmCqoL-36hWygdl11kiCoHbnfzaanpt0C0pXiz6lzCD8WoSzWqGZyZWlPs6q2Q7NhL5logiJJcn7CSpUViUTQl9t6k2od7nLrCq5f5ziR8wgdBN-D8mbbHEgCU-6eAnkijX4C0pXKIElzCD8kAfuoc1uzsmi3KcRR664WlPs64zOjggiJJcXRs5Q5cAt6-y88NnLrCqoLE54lqmeIDipXAyMxwSZSI04EkybJ_GBzKL82nicdxb62KneINxrXAlOUaJeCpYPGCxhAldw7QfdQ_KPdBG2d8IIEmdwb6fzxQluXMzKMCBeABewzSGCxhAldQzSfdQSMrdA1HG8IWAILwEHzUi0LbjfcJ2WWy3ZoBdOt7ALU55xBeh7wd4YWQcknhOQcKCryQ-NZf7Nf1mfIS3e7H5RmTt7oMUVUwmJOefjK65J-QH5xdOB-u-GH-uz5OC6hOnhvd47UoJUPfW1DUe9fO",
  "PpSMO8q1_Q6EzADffHg7Tf99KB3Zc7_2RKU_4RfOIeHdOp6kOOnpHlfffv1DzWQTcWNZc7roxlSpcQNUv4xc7jnhSAldfBFNLv6DzJ9-EJeXaORnEncxBehY5M6AsNrYBszGKWSRbgrjqCWFp9SyVSYncpcTZrlcMnMIaTTyjZMEsWZdX33iyPktrW7lhZKeSfiRlcCpfnSmcFnkocFsiU1XRimoISSPiAnkAY5YJB7yZZZ1pajwr2S11bNTyjZ9myncrSyGTVCeQK1Yg4JBUSbZVaTYi7OgXZFRhpZlNYITzOATNshJIbcc3OTI8J1T0LKtRRrRJa_YCTacAkGdBw4Ss_wYTsxbpGd0McRCHZKBBFwS8dhpkntOw4VsWp-RYJJKRsbJCHdvYCRsuA89dRZ4VspHi9uQpEmS-RshhYZ1VbcaTNieLcOCGZ9dp5TERsHPyRY6cR5ecpcpZlppQCvYiOa6M-TseL69B2PIMKcYYisOM1hY0hRSa_kPUKLsicZPriicnYAWZHNwtIDSC4anOAyTZGZ0im-bqlBdMmqJEi-uX3FpXApPyLGEbpfooy5crma5Gwd-CfLEDka230rf88NnfX77AqQ0o4GMXs1eN_hff1a8pXN9tNE887-uuoS7cpmJnfDnq7q9777q7pynf78lX4y_TjaRiy2cpmp-uX7N6GgeMzFU_vyuK02DGKtAzkp9zMGc0IFG16NxlKcECsTnSUKPRutHFZQFc7TirHTqChcLZgicrqCMKxRytITSxiZJSi7JnOYiSAm62sEcpDbLlQuL5hyBbRlwTt31uvaDkApLrjQRLzzytav-CPLNigxajhwxTldyVLphYCUG8KxW24qBUu7yCABIPHARTPHARTHiPSTHES4YJABY_voIOPHvFe_nwF_iJiPSTXHAqTHAB-XpjPwO1BBA_1zF6PnwF4YJ7BOPX9B5b38BgIH7BA_X9BS_vCAtSPHAdHPHART1FSeT1JAY_9FK6PnwFcXZkB0P1wFgIH7BOP1zFlMYxFrF3FSSTHESMDZGScX3JA0PnFSgInjPwO1BBA_1zFBjJiB0P1wFHMILAwT1BBe_vFKS_9zP3TPEApHPeBpHPeBYD3FSoX3jPIPHyFiX3BBe_nwFIInCSIPHyFXXAoIiXJ7BA_n8BM_XxFYTngPcXZhPwOHvFCPnwFS_H7BCPXxFuX3jPaIPfSqT18BIP1wFNMYhPgIXDSwO1BBA_n8BCPnwFS_nCS0P1wFvXojBgInJAwTH7BOPHvFe_PqI_XY9BS_XGScX38BG_HLAwTH7BOPHvFe_HIAaIPfSIP1wFY_nFSgIHlBwO1BBe_vrICIHiB_aZGSOI18BY_fhSHMIvFYTXGSqD38BIP1wFY_1zFlMo8BCPnwFS_ngP4YpCSqD3BBlMYxF5bZGSBbZkPIP1wFY_XhPwO1BBA_1zFlMwFKxFRGZq2VF7N_OF7N_OF7N_OF7N_uJ7J0vJ7J0vJ7J0vJ7J0PE7vveJ7FGfy9pv8F7NweJ7FGPz99Gfy9pv8F79G9F7Twu1ApvW26NweJ7pvuI7FGPz99GPE83-OE83-OE83-OE83-Ox7MtOD80LwSAnL9SAR_8y7h1vkAXJPx7X_OD8nL9SAR_8y7osOD8n1vkAX_OD8n1vkAdJPx7X_OD8n1vSAnLXK6UxmJ62jZ8UumJeT-mpfTumhiSnbJeT8jRkWGn3UE38ClWumBlWyiho7d1fo7d1fo7d1fo7d1nR7kz8y7n1HQJtLvSAR_8y7h19E8dJ9kAX_OD8n1vkAdJ9kA",
  "XJPx7X_8E8XJPx7X_OD8wKQx7X_8E8dJHeTsiJ9UomJ9UEjpcTomh2X22100O0GK0k2m30K9HFE6o1R9knvVJlM2I000m00S20t2Y2WA9gBXS9Q9HyEqnXxE6o1DEMtnDEvRwrIS2W10O0Gs2k2mzEUivoIvRQqI00G20U0WA9acHYDMt1ZDkn9VJZM20060Wr2uMG20U0WxE6o199kt1ZDUBvoI5SQqI60WJ0uM0L0Y2GT9aBXxE6onC9et1I060W10Y2mL0U0mGEktnC9Gt1DEetnDEC3ArI5SgpI00m00S2W10e2030I0m30Oc9rIHMoZnJPEt7Z29t7Z29t7Z29t7Z2HZ7Qy0s7Wp0a7c2nK800m00S20t2wnHyEqn1DE0onDEmBXJ0k2WxEsB1R9UinR9HMgWJM2WJ0e2mt2Y2mL0I0m30K9HT9Q9HrCStnGEktnC9GtnZDen1zEkn1sCfM2q2M2Wr2Y2mGEkn1sCmB9VJR_8y7h19E8nL9SAR_8y7h19E8tL9kAXJ9y7h1vSAR_8y7h19E8XJPx7X_OD8n1vkAdJ9SAR_OD8n1HeT4npcTomh2X4np7U4n3fTsi3AU38imWumhESWM0I0cM000S20t2C0mt2Y2mL0U0WA9gBXqCwnHyEIinGE89nzEOBnwEUc1sC5SQqIS2W10e2mL0I0WS9YtnGE891R9Gt1DE6inwEknnR9W99YJNSYSGlMoI0e2Gs2-MGK0k2GT9YtXxE891WDc9nsCMt1GEE9vVJHSArIM2WJ0C0mt2Y2m30K9HB9OcnzEE9voIHM2RGZtUvssCsKcKcLkn8oSir_2fO8jMv58r0vN853PsATKv58r0vN853PaATKHs6r0vN8SteO8ZKv58r0vN853PsAl0f68_2fO8sRQsATK1q200W10-MG20K9HFEYtXxEIinGEktnDEW9vrIO0m30gBHYD89nC9Mt1GEE9PXJiMWJ0C0030k2G20U0WS9gcnC9GtnZDen1zEMtnpCknPXJ000WDktnR9HSAVJHMgWJTMY8U-mhmW8jJ6UomJ9UumJeTd5qcT98K9UumJsi4drZnQcLknhhc8Ukrv-WsiJ6UKjh2Xyip7UsiJ6UKj3fTsiJ6UKjxiWsi3AUApKmiucLenwdLMccoKkn6CMviuoaXcnu6inqSKknMSaOcftU7pxvOF7vvuI7TwOz9pv8F7NweJ7FGPz9bFPE7vv81AvvuI7Twu1A9GPE7Nwu1AbFPE7NweJ7hFPm7R_OD80LASAR_8y7h1vSAR_8y7h1vkAnL9SAR_8y7osOD8n1HdIdJ9SAR_8y7h19E8tLvSAXJ9y7h19E8w_ukAdJX8UumJeTv5qfTbbR0Xv5qR7kz8y7h19E8tLvSAR_8y7h19E8dJ9kAX_OD8n1vkAdJ9kAXJPx7X_Gs6h19E8X_OD8n1vkAdJ9kAXJPx7X_OD8Uo8E82jJ6Uz7agTyi37U2jpcTL8qK822HG8i21I000Wr2C0030Y2mL0K9HFE6o199kt1R9etnDEE9nR9vRAoITMwrI00mI060WJ0e2GK0U0GB9qnXxE6onU9etnDEZMYJ0O0G20aBnGEkt1wEknn99UB9rINSYxFY2m30gB1zE0on99mBvoI00m00iMWJ0uMW10Y2WA9StnWDHMgpINSo00S2030Y2mL0U0WEEStnGEsB1zEMt1GE_Ro00S2W10e2030Y2mGEkt1DEetnDEW99rI5SgpIRd2q2e2030qnnGEen1GEfMADpkdTvsQcrKcv-0S6Wy0H860WJ0e2G20",
  "wnXS9qn1DE0o9VJ5SoI0S2W10e2030Y2mL0Q9HyEqnnGEsBnC9GtnZDennDEUB1C9vRAoI5SYr2C00L0oMG20K9HB9StnGEkt1wEen1zEOi1GEknvYJG2m00C0GK0I0mGEkt1GEE91U9fMAVJHMQqIR_8y7h19E8dJ9kAXJPx7X_OD8n1vkAXJPx7X_mw6h1nJ6n1vSAnLPx7h19E8R_OD8n1vkAdJ9SAR_OD8n1X8U-m3fTxXJeT4np7UKjpcTGnZgT2jpcTG20t2C0mt2Y2mL0U0WA9wnXXDIinGE89nU9ktnR9NMAoIlMo00C00L0O0mt2gBHyEOcnGEc91wEennwEknnR9W9vVJfMo00iMW10e2Gs2Y2mL0gBXxEOcnGEkt1DEMt1ZD0onR9HSArIBSo00S2W10O0WA9wnXS9Q91pCkt1GEfM2RGaTyzsoD-3tqpaXcjik68_2nn7jMv58r0vN853frAl0f68_2fO8l0f68_21t6SteO8ZKfrAAnu58_2HR6pMPaAjMv58r0vN8ZKfZAG2000C0mt2U0GFEYtXxEIi1pC6onDEW9vrII32q2O0m30qnXxE891R9c91wEennwE0on99mBnR9S_XJ0uMW10O0mL0K9HT9gcHYDc91wEennpCkn1sCUB1q200mI0C0mL0I0m30Yt199OBnR9HSAoI5SwrIZMocTKjZdT7YJeT8jpcT38K6UumJeT4nJen0CMpihhscTomh2XEjp7U8jpcTKjx-Wsi3AUomZgTEj3vDGn3WnwSKMccoaoiCqyBpgCsYZftk7t5OkzoXNk9SvDBGQrlhSUDXBlP1Ih-Tbph9SvDBGQrlhSUDXBlP1Ih-TbpRz1NQW5IHQey1aT2FHgT262ybGm4hFuI3HQey1cGoFHybGm4hFuI3HQey1aTIjJ-9262sGWl42cOz1NQ8I3bFGwNaToFHsGGm4hF0xNNQ8I3bFm4I2cOz1NQ8I3bFm4IaT2FHgTo62ybOg2e1hn3JUef28CIT5JLen3JUWOHDLW-JcEGT5JL0DODUOo3DLmNHwVQg2DUOo3DLW-J8Coq1JLen3JUef2ECYS5JL0DODUOo34Bgf2wV2q1ahGT5dhEVrphURc9pSOY7FiNYnLQmI1FCSrdhEVrph6ASMXhKY3JyuXoZJRSSXhGJpS5lrqhEyhXhkuc3JKCSpPwrXjPwkI_PI9S9MwvhIICdhXhkTrcZRS7ToeR7ZomvJaK2BLUfY-7Zx0RJToeR7ZoWwJaK2BLsPW-7w_OS7ToeR7ZoGQJEVYaIOf2E3q_OS7ToeR7ZoWaIOfIbIsPW-7w_OS7ORgJ6TxOK6IRovJgKoBLq_OS7ToeR7ZoGQJEVYaIOfIbIUf2E3HNkxofN-zoHVSJeMORAKFtwJjrHTCgJgLvefHTFgkYEJjNNEzoZNEKeNV42R7mSHZvPyIZDmyFZxWgKjgNUCg1ILwoPgDwoTNEzoZN-KevUCKerlCFZtsQuMPXQCgScCwoTNU2cYOJ1RLtAMjJg5raeDJiB_apgPeTXKAOIHABfMAFKkT1zFHjR_PrF3jP4Y3wFjXwCKiXxrINjR_PviheTlPJESeDpgP4Y3jBaIPfScXZkBXXwoIjXArIdXAFKSDJLAlMQqI6PnwF1GxgTlFxdTfF3FSSTHIA4YBoIvXoFSpXwrI_XowFBjBdT_QiCZrFyHZBFSMZTRCHZ3EywXfFyEZRIDeh_UjchPpuZ7PyuR68L238U09R6VyWVJPyuR68LY6LELYL3O0n38PpuZ7PyuR6sR2fIweIM3",
  "U09R6VyWVJPyuR68LofIU09R6Vy8Z7Vp0fIqeofIoQ038PpuZ7yRAZ7Vp0mJ8LI7LO0HESCIPFRG_9CKfMwCKTMAFKpXQ_PYD3FSoX3jBqD38BjXAoITMoFSpXQqIlFRfTrFheTCIPFRcXJABHMYhP-XxrIZMwdTrFheTaIXkB0PHABG_voIHbBoISD3BBe_vrI_Xo8BHjBwofN-zoj25ePGOZ0R_PK1R1ITFgTNEzoJmyIZDmSuMHQKzong5xoPg5weHNkxoNNEzoZN-zo6Dp2RvPSuM_PCBKONcpaGcixoL2zsMwChKjVgDMjhgzzXREyHZXQSAZtPSGZRIDehpUDkh2j3jE-m3fTsi3AUKjBKOV4JTE6svKOt43vDzbBkS4nJ6UF2haO92xZOumpmEd2xcOQfflS7YRmShbRFStbZ8Uqr1UEKf9ZOb4ZdTspHBDhbRFStbBDSnb3REKjxHOX2J9Ud23VZqS4hZoR4SZcR4VZeSafZYSiw612vG8KMQx6ONYOLUNY24QWmn7Lt8G872Px64hoxIQWew612vG8KMQx6GWonIONYOLUN2n7Lt8G872XoIRtWOL8-mn7Lt8G872Px6GWI1KONoxIAhY24Lt8G872Px6EMI1K4hoxIAhY24EMnjSUXvKTFdAyKNSwkPJnxhPoFxwRcFZ0QrVxVJC3wvKiFRxKNSIfAGL9kPDnxkPVDR7U7nBhPbDh6UqbpBCTV3EC_RgwKFdgWJXdwYJVDR7UPDxKT0cZ0QmX9vKU3AyK-K9kPtDRjPbD3mEP4xHOEl9cOd2xcOzbRmSxXBDSbb3jEUpvlWF8yHOb4hIOwrnfT6sn9DskvcOWf9GSzbRmSlXRFStbhESj54UEF8iaO92xZOL2ZdTEj37U6sPbOd2xcO8lvDShbRFStbBDSrXBkSp5akEmpnCDEl17UEfvcO1Y3SZ4SKjZSSqhZeSacZoRKaZNN-tZNV42RDmCIZSOBBKbgrraxHDzolNEKeNVy0c5QSHZ4Oh-bJmyIZYOR_btswFZAOh9KVg5LqJgbMqfHTLju6zwofNUyop2jIevPyIZxlyFZwC3OqZHDGgfHzwoHVCKe6Dh-bYORuMxWY3RCDBBKlHLzoON-NZXEiCZ5RytXpQSyXTRi1YdQywXjQyqXHJDEgpUrSZgTaTZMSqVZYSCeoDLUgoVLECat-ypddXCsdNoiJcgW-1j5KDVgReD9ab-iAaP-qmQHoCmZrTiJc7vQANDUi2jpJT0jaWEYg9eDeoDL-eoPLUgoVLEpdFXysdqLRKc2Bx8NzawcKwLZNPpJD4jHKrOfIBDVgReDeoDL-eoVL-9aV-Csd0MxBNbvwVgRe5kbWRqSZiRKgZqSafZOTKUZ-RCEZXESpX_EiIZ1GyQZJPyEZpESGgDTjrh1TTshBRytX5FSJZZFirXJPSGZJTDqh9UTJg1TzthpU5"
]

def d7CoreWitnessChunkSize : Nat := 1800

def d7CoreWitnessCharAt (index : Nat) : Char :=
  let chunk := d7CoreWitnessChunks.getD (index / d7CoreWitnessChunkSize) ""
  String.Pos.Raw.get! chunk ⟨index % d7CoreWitnessChunkSize⟩

def d7CoreWitnessCodeAt (item : Nat) : Nat :=
  let bitStart := item * witnessBits
  let digitStart := bitStart / 6
  let shift := bitStart % 6
  let window := (List.range 3).foldl (fun value digit =>
    value + alphabetValue (d7CoreWitnessCharAt (digitStart + digit)) *
      2 ^ (6 * digit)) 0
  window / 2 ^ shift % 2 ^ witnessBits

def d7RootFreeWitnessCode (position : Fin 3227) : Nat :=
  d7CoreWitnessCodeAt position.val

def d7RootContainingWitnessCode (position : Fin 2396) : Nat :=
  d7CoreWitnessCodeAt (3227 + position.val)

/-! ## K7 blocker reconstruction -/

def d7RootFreeSourceIndex (position : Fin 3227) : Nat :=
  (d7CoreSourceIndex (d7RootFreeCorePosition position)).val

def d7RootFreeLocation (position : Fin 3227) : List Nat × Nat :=
  (d7BlockLocation (d7RootFreeSourceIndex position - d7BlockClauseStart)).getD
    ([], 0)

def d7RootFreeItem (position : Fin 3227) : List Nat :=
  (d7RootFreeLocation position).1

def d7RootFreeCatalogueIndex (position : Fin 3227) : Nat :=
  (d7RootFreeLocation position).2

def d7RootFreeEmbedding (position : Fin 3227) : MotifEmbedding :=
  fun vertex => Fin.ofNat 12 ((d7RootFreeItem position).getD vertex.val 0)

def d7RootFreeRepresentativeIndex (position : Fin 3227) : Fin 6 :=
  ⟨d7RootFreeWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def d7RootFreePermutationRank (position : Fin 3227) : Fin 5040 :=
  Fin.ofNat 5040 (d7RootFreeWitnessCode position / 6)

noncomputable def d7RootFreeRepresentative (position : Fin 3227) :
    RepresentativeWitness :=
  representativeWitness (d7RootFreeRepresentativeIndex position)

def d7RootFreeCube (position : Fin 3227) : Cover6Cube :=
  permuteCube (decodedPermutation (d7RootFreePermutationRank position))
    (representativeCubeAt (d7RootFreeRepresentativeIndex position))

def D7RootFreeFiniteCheck : Prop :=
  dataLength d7CoreWitnessChunks = 14058 ∧
  (∀ position : Fin 3227,
    d7RootFreeWitnessCode position < witnessCodeLimit) ∧
  (∀ (position : Fin 3227) (left right : MotifVertex),
    d7RootFreeEmbedding position left = d7RootFreeEmbedding position right →
      left = right) ∧
  (∀ position : Fin 3227,
    d7SelectedCoreClause (d7RootFreeCorePosition position) =
      cubeDimacsBlocker (d7RootFreeEmbedding position)
        (d7RootFreeCube position))

instance d7RootFreeFiniteCheckDecidable :
    Decidable D7RootFreeFiniteCheck := by
  unfold D7RootFreeFiniteCheck
  infer_instance

/-! ## Projected K6 blocker reconstruction -/

def d7RootContainingSourceIndex (position : Fin 2396) : Nat :=
  (d7CoreSourceIndex (d7RootContainingCorePosition position)).val

def d7RootContainingLocation (position : Fin 2396) : List Nat × Nat :=
  (d7LocalLocation
    (d7RootContainingSourceIndex position - d7LocalClauseStart)).getD ([], 0)

def d7RootContainingItem (position : Fin 2396) : List Nat :=
  (d7RootContainingLocation position).1

def d7RootContainingCatalogueIndex (position : Fin 2396) : Nat :=
  (d7RootContainingLocation position).2

def d7RootContainingNeighbourCount (position : Fin 2396) : Nat :=
  d7NeighborCount (d7RootContainingItem position)

def d7RootContainingProjectedCube (position : Fin 2396) : Cover6Cube :=
  let cube := d7LocalCubeAt (d7RootContainingNeighbourCount position)
    (d7RootContainingCatalogueIndex position)
  { ones := cube.1, fixed := cube.2 }

def d7RootContainingProjectedEmbedding (position : Fin 2396) :
    MotifEmbedding :=
  fun vertex =>
    Fin.ofNat 12 ((d7RootContainingItem position).getD vertex.val 0)

def d7RootContainingEmbedding (position : Fin 2396) : MotifEmbedding :=
  fun vertex =>
    if vertex.val = 0 then 0
    else Fin.ofNat 12
      ((d7RootContainingItem position).getD (vertex.val - 1) 0)

def d7RootContainingRepresentativeIndex (position : Fin 2396) : Fin 6 :=
  ⟨d7RootContainingWitnessCode position % 6, Nat.mod_lt _ (by decide)⟩

def d7RootContainingPermutationRank (position : Fin 2396) : Fin 5040 :=
  Fin.ofNat 5040 (d7RootContainingWitnessCode position / 6)

noncomputable def d7RootContainingRepresentative (position : Fin 2396) :
    RepresentativeWitness :=
  representativeWitness (d7RootContainingRepresentativeIndex position)

def d7RootContainingFullCube (position : Fin 2396) : Cover6Cube :=
  permuteCube (decodedPermutation (d7RootContainingPermutationRank position))
    (representativeCubeAt (d7RootContainingRepresentativeIndex position))

def d7RootContainingAmbientVertex
    (position : Fin 2396) (vertex : MotifVertex) : Nat :=
  (d7RootContainingItem position).getD (vertex.val - 1) 0

def D7RootContainingFiniteCheck : Prop :=
  (∀ position : Fin 2396,
    d7RootContainingWitnessCode position < witnessCodeLimit) ∧
  (∀ position : Fin 2396,
    d7SelectedCoreClause (d7RootContainingCorePosition position) =
      cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position)) ∧
  (∀ (position : Fin 2396) (left right : MotifVertex),
    d7RootContainingEmbedding position left =
      d7RootContainingEmbedding position right → left = right) ∧
  (∀ (left right : MotifVertex), 0 < left.val → left < right →
    projectedVertex left < projectedVertex right) ∧
  (∀ (position : Fin 2396) (vertex : MotifVertex), 0 < vertex.val →
    d7RootContainingEmbedding position vertex =
      d7RootContainingProjectedEmbedding position
        (projectedVertex vertex)) ∧
  (∀ (position : Fin 2396) (left right : MotifVertex),
    0 < left.val → left < right →
    (d7RootContainingFullCube position).fixed.testBit
        (graph6EdgePosition left.val right.val) = true →
    (d7RootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (d7RootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (d7RootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val)) ∧
  (∀ (position : Fin 2396) (vertex : MotifVertex), 0 < vertex.val →
    1 ≤ d7RootContainingAmbientVertex position vertex ∧
      d7RootContainingAmbientVertex position vertex < 12) ∧
  (∀ position : Fin 2396,
    (d7RootContainingEmbedding position 0).val = 0) ∧
  (∀ (position : Fin 2396) (vertex : MotifVertex), 0 < vertex.val →
    (d7RootContainingEmbedding position vertex).val =
      d7RootContainingAmbientVertex position vertex) ∧
  (∀ (position : Fin 2396) (right : MotifVertex), 0 < right.val →
    (d7RootContainingFullCube position).fixed.testBit
        (graph6EdgePosition 0 right.val) = true →
    (d7RootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (d7RootContainingAmbientVertex position right ≤ 7))

instance d7RootContainingFiniteCheckDecidable :
    Decidable D7RootContainingFiniteCheck := by
  unfold D7RootContainingFiniteCheck
  infer_instance

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 100 in
theorem d7CorePayloadFiniteChecks :
    D7RootFreeFiniteCheck ∧ D7RootContainingFiniteCheck := by
  native_decide

theorem d7RootFreeFiniteChecks : D7RootFreeFiniteCheck :=
  d7CorePayloadFiniteChecks.1

theorem d7RootContainingFiniteChecks : D7RootContainingFiniteCheck :=
  d7CorePayloadFiniteChecks.2

theorem d7RootFreeEmbedding_injective (position : Fin 3227) :
    Function.Injective (d7RootFreeEmbedding position) :=
  d7RootFreeFiniteChecks.2.2.1 position

theorem d7RootFreeClause_eq (position : Fin 3227) :
    d7SelectedCoreClause (d7RootFreeCorePosition position) =
      cubeDimacsBlocker (d7RootFreeEmbedding position)
        (d7RootFreeCube position) :=
  d7RootFreeFiniteChecks.2.2.2 position

theorem d7RootFreeCube_orbit (position : Fin 3227) :
    CubeInOrbitOf (d7RootFreeCube position)
      (d7RootFreeRepresentative position).cube := by
  refine ⟨decodedPermutation (d7RootFreePermutationRank position), ?_⟩
  unfold d7RootFreeRepresentative
  rw [representativeWitness_cube]
  rfl

noncomputable def d7RootFreeBlockerWitness (position : Fin 3227) :
    RootFreeBlockerWitness
      (d7SelectedCoreClause (d7RootFreeCorePosition position)) :=
  { embedding := d7RootFreeEmbedding position
    cube := d7RootFreeCube position
    representative := (d7RootFreeRepresentative position).cube
    inner := (d7RootFreeRepresentative position).inner
    motif := (d7RootFreeRepresentative position).motif
    motif_mem := (d7RootFreeRepresentative position).motif_mem
    embedding_injective := d7RootFreeEmbedding_injective position
    orbit := d7RootFreeCube_orbit position
    representative_forces := (d7RootFreeRepresentative position).forces
    clause_eq := d7RootFreeClause_eq position }

theorem d7RootContainingProjectedClause_eq (position : Fin 2396) :
    d7SelectedCoreClause (d7RootContainingCorePosition position) =
      cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position) :=
  d7RootContainingFiniteChecks.2.1 position

theorem d7RootContainingEmbedding_injective (position : Fin 2396) :
    Function.Injective (d7RootContainingEmbedding position) :=
  d7RootContainingFiniteChecks.2.2.1 position

theorem d7RootContainingFullCube_orbit (position : Fin 2396) :
    CubeInOrbitOf (d7RootContainingFullCube position)
      (d7RootContainingRepresentative position).cube := by
  refine ⟨decodedPermutation (d7RootContainingPermutationRank position), ?_⟩
  unfold d7RootContainingRepresentative
  rw [representativeWitness_cube]
  rfl

theorem d7ProjectedVertex_lt
    (left right : MotifVertex) (hleft : 0 < left.val)
    (hordered : left < right) :
    projectedVertex left < projectedVertex right :=
  d7RootContainingFiniteChecks.2.2.2.1 left right hleft hordered

theorem d7RootContainingEmbedding_nonroot
    (position : Fin 2396) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    d7RootContainingEmbedding position vertex =
      d7RootContainingProjectedEmbedding position
        (projectedVertex vertex) :=
  d7RootContainingFiniteChecks.2.2.2.2.1 position vertex hvertex

theorem d7RootContaining_nonroot_bits
    (position : Fin 2396) (left right : MotifVertex)
    (hleft : 0 < left.val) (hordered : left < right)
    (hfixed : (d7RootContainingFullCube position).fixed.testBit
      (graph6EdgePosition left.val right.val) = true) :
    (d7RootContainingProjectedCube position).fixed.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) = true ∧
      (d7RootContainingProjectedCube position).ones.testBit
          (graph6EdgePosition (projectedVertex left).val
            (projectedVertex right).val) =
        (d7RootContainingFullCube position).ones.testBit
          (graph6EdgePosition left.val right.val) :=
  d7RootContainingFiniteChecks.2.2.2.2.2.1
    position left right hleft hordered hfixed

theorem d7RootContainingAmbientVertex_bounds
    (position : Fin 2396) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    1 ≤ d7RootContainingAmbientVertex position vertex ∧
      d7RootContainingAmbientVertex position vertex < 12 :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.1
    position vertex hvertex

theorem d7RootContainingEmbedding_root_val (position : Fin 2396) :
    (d7RootContainingEmbedding position 0).val = 0 :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.1 position

theorem d7RootContainingEmbedding_nonroot_val
    (position : Fin 2396) (vertex : MotifVertex)
    (hvertex : 0 < vertex.val) :
    (d7RootContainingEmbedding position vertex).val =
      d7RootContainingAmbientVertex position vertex :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.2.1
    position vertex hvertex

theorem d7RootContaining_root_bit
    (position : Fin 2396) (right : MotifVertex)
    (hright : 0 < right.val)
    (hfixed : (d7RootContainingFullCube position).fixed.testBit
      (graph6EdgePosition 0 right.val) = true) :
    (d7RootContainingFullCube position).ones.testBit
        (graph6EdgePosition 0 right.val) =
      decide (d7RootContainingAmbientVertex position right ≤ 7) :=
  d7RootContainingFiniteChecks.2.2.2.2.2.2.2.2.2
    position right hright hfixed

/-! ## Base and unit clauses -/

theorem d7LeftTriangleItem_valid (index : Nat) (hindex : index < 35) :
    let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 7 3).getD
        index []
    item.length = 3 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 8) ∧ item.Nodup := by
  native_decide +revert

theorem d7RightTriangleItem_valid (index : Nat) (hindex : index < 4) :
    let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 8 4 3).getD
        index []
    item.length = 3 ∧
      (∀ value ∈ item, 8 ≤ value ∧ value < 12) ∧ item.Nodup := by
  native_decide +revert

theorem d7BaseClause_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (index : Nat) (hindex : index < d7BaseClauseCount) :
    CNF.Clause.eval coloring (dimacsClause (d7BaseClause index)) = true := by
  by_cases hfour : index < 660
  · let item :=
      (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 11 4).getD
        (index / 2) []
    have hitemIndex : index / 2 < 330 := by omega
    have hvalid := fourBlockItem_valid hitemIndex
    change item.length = 4 ∧
      (∀ value ∈ item, 1 ≤ value ∧ value < 12) ∧ item.Nodup at hvalid
    by_cases hpositive : index % 2 = 1
    · have hnotBlue := hfree.2 item hvalid.1
          (fun value hvalue => (hvalid.2.1 value hvalue).2)
          hvalid.2.2
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_true_edge 12 item coloring hnotBlue
      obtain ⟨left, right, hleft, hright, hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 item dimacsVariable hvariable
      have hsatisfied := signedPairClause_eval_true coloring item true
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [d7BaseClause, hfour, hpositive, item,
        LRATCatcher.Tests.R44Cover6Master8IndexedSource.baseClause] using
        hsatisfied
    · have hnotRed := hfree.1 item hvalid.1
          (fun value hvalue => (hvalid.2.1 value hvalue).2)
          hvalid.2.2
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_false_edge 12 item coloring hnotRed
      obtain ⟨left, right, hleft, hright, hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 item dimacsVariable hvariable
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [d7BaseClause, hfour, hpositive, item,
        LRATCatcher.Tests.R44Cover6Master8IndexedSource.baseClause] using
        hsatisfied
  · by_cases hleftBlock : index < 695
    · let item :=
        (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 1 7 3).getD
          (index - 660) []
      have hvalid := d7LeftTriangleItem_valid (index - 660) (by omega)
      change item.length = 3 ∧
        (∀ value ∈ item, 1 ≤ value ∧ value < 8) ∧ item.Nodup at hvalid
      let ambient := 0 :: item
      have hnotRed := hfree.1 ambient (by simp [ambient, hvalid.1])
        (by
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · omega
          · have := hvalid.2.1 value hvalue
            omega)
        (by
          simp only [ambient, List.nodup_cons]
          exact ⟨by
            intro hzero
            have := hvalid.2.1 0 hzero
            omega, hvalid.2.2⟩)
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_false_edge 12 ambient coloring hnotRed
      obtain ⟨left, right, hleftAmbient, hrightAmbient,
          hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 ambient dimacsVariable hvariable
      have hright : right ∈ item := by
        rcases List.mem_cons.mp hrightAmbient with hzero | hright
        · subst right
          omega
        · exact hright
      have hleft : left ∈ item := by
        rcases List.mem_cons.mp hleftAmbient with hzero | hleft
        · subst left
          have hroot := hrootPositive right
            (hvalid.2.1 right hright).1 (hvalid.2.1 right hright).2
          have hrootRaw : coloring (edgeVar 12 0 right) = true := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item false
        hleft hright hleftRight (by
          have := hvalid.2.1 right hright
          omega) hcolor
      simpa [d7BaseClause, hfour, hleftBlock, item] using hsatisfied
    · have hrightIndex : index - 695 < 4 := by
        unfold d7BaseClauseCount at hindex
        omega
      let item :=
        (LRATCatcher.Tests.R44Cover6Master8IndexedSource.combinations 8 4 3).getD
          (index - 695) []
      have hvalid := d7RightTriangleItem_valid (index - 695) hrightIndex
      change item.length = 3 ∧
        (∀ value ∈ item, 8 ≤ value ∧ value < 12) ∧ item.Nodup at hvalid
      let ambient := 0 :: item
      have hnotBlue := hfree.2 ambient (by simp [ambient, hvalid.1])
        (by
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · omega
          · exact (hvalid.2.1 value hvalue).2)
        (by
          simp only [ambient, List.nodup_cons]
          exact ⟨by
            intro hzero
            have := hvalid.2.1 0 hzero
            omega, hvalid.2.2⟩)
      obtain ⟨dimacsVariable, hvariable, hcolor⟩ :=
        exists_true_edge 12 ambient coloring hnotBlue
      obtain ⟨left, right, hleftAmbient, hrightAmbient,
          hleftRight, rfl⟩ :=
        cliqueEdgeVars_mem 12 ambient dimacsVariable hvariable
      have hright : right ∈ item := by
        rcases List.mem_cons.mp hrightAmbient with hzero | hright
        · subst right
          omega
        · exact hright
      have hleft : left ∈ item := by
        rcases List.mem_cons.mp hleftAmbient with hzero | hleft
        · subst left
          have hroot := hrootRight right
            (hvalid.2.1 right hright).1 (hvalid.2.1 right hright).2
          have hrootRaw : coloring (edgeVar 12 0 right) = false := by
            simpa [coloringEdge, hleftRight] using hroot
          simp [hrootRaw] at hcolor
        · exact hleft
      have hsatisfied := signedPairClause_eval_true coloring item true
        hleft hright hleftRight (hvalid.2.1 right hright).2 hcolor
      simpa [d7BaseClause, hfour, hleftBlock, item] using hsatisfied

theorem d7SelectedBaseClause_eq (position : Fin 168) :
    d7SelectedCoreClause (d7BaseCorePosition position) =
      dimacsClause (d7BaseClause
        (d7CoreSourceIndex (d7BaseCorePosition position)).val) := by
  native_decide +revert

def d7SelectedUnitTailPosition (position : Fin 16) : Fin 21 :=
  ⟨(d7CoreSourceIndex (d7UnitCorePosition position)).val - f7ClauseCount,
    by
      have h := d7UnitCoreSourceIndex_range position
      unfold branchClauseCount r34UnitClauseCount at h
      omega⟩

theorem d7SelectedUnitClause_eq (position : Fin 16) :
    d7SelectedCoreClause (d7UnitCorePosition position) =
      (branchSource fgraveGowCatalogueIndex).clauseAt
        ⟨f7ClauseCount + (d7SelectedUnitTailPosition position).val, by
          change f7ClauseCount + (d7SelectedUnitTailPosition position).val <
            branchClauseCount
          dsimp [branchClauseCount, f7ClauseCount, r34UnitClauseCount]
          omega⟩ := by
  native_decide +revert

/-! ## Projected full-lift semantics -/

theorem d7RootContainingProjected_false_gives_full_match
    (coloring : Nat → Bool)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (position : Fin 2396)
    (hfalse : CNF.Clause.eval coloring
      (d7SelectedCoreClause (d7RootContainingCorePosition position)) = false) :
    CubeMatchesLocal
      (embeddedLocalEdges coloring (d7RootContainingEmbedding position))
      (d7RootContainingFullCube position) := by
  have hprojectedFalse : CNF.Clause.eval coloring
      (cubeDimacsBlocker (d7RootContainingProjectedEmbedding position)
        (d7RootContainingProjectedCube position)) = false := by
    rw [← d7RootContainingProjectedClause_eq position]
    exact hfalse
  have hprojectedMatch :=
    (cubeDimacsBlocker_eval_false_iff coloring
      (d7RootContainingProjectedEmbedding position)
      (d7RootContainingProjectedCube position)).1 hprojectedFalse
  intro left right hordered hfixed
  by_cases hleftZero : left.val = 0
  · have hleft : left = 0 := Fin.ext hleftZero
    subst left
    have hrightPositive : 0 < right.val := hordered
    let ambient := d7RootContainingAmbientVertex position right
    have hambientBounds :=
      d7RootContainingAmbientVertex_bounds position right hrightPositive
    have hrootColor : coloringEdge 12 coloring 0 ambient =
        decide (ambient ≤ 7) := by
      by_cases hneighbor : ambient ≤ 7
      · simpa [hneighbor] using hrootPositive ambient
          hambientBounds.1 (by omega : ambient < 8)
      · simpa [hneighbor] using hrootRight ambient
          (by omega : 8 ≤ ambient) hambientBounds.2
    have hembeddingRoot := d7RootContainingEmbedding_root_val position
    have hembeddingRight := d7RootContainingEmbedding_nonroot_val
      position right hrightPositive
    have hdistinct : d7RootContainingEmbedding position 0 ≠
        d7RootContainingEmbedding position right := by
      intro hequal
      have hvalues := congrArg Fin.val hequal
      rw [hembeddingRoot, hembeddingRight] at hvalues
      exact (by omega : False)
    have hambientColor := coloring_symmetricEdgeVarTwelve coloring
      (d7RootContainingEmbedding position 0)
      (d7RootContainingEmbedding position right) hdistinct
    rw [hembeddingRoot, hembeddingRight] at hambientColor
    have hrequired := d7RootContaining_root_bit position right
      hrightPositive hfixed
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingEmbedding position 0)
      (d7RootContainingEmbedding position right)) = _
    exact hambientColor.trans (hrootColor.trans hrequired.symm)
  · have hleftPositive : 0 < left.val := by omega
    have hbits := d7RootContaining_nonroot_bits position left right
      hleftPositive hordered hfixed
    have hprojectedOrdered := d7ProjectedVertex_lt left right
      hleftPositive hordered
    have hmatch := hprojectedMatch (projectedVertex left)
      (projectedVertex right) hprojectedOrdered hbits.1
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingEmbedding position left)
      (d7RootContainingEmbedding position right)) = _
    change coloring (symmetricEdgeVarTwelve
      (d7RootContainingProjectedEmbedding position (projectedVertex left))
      (d7RootContainingProjectedEmbedding position (projectedVertex right))) = _
      at hmatch
    have hrightPositive : 0 < right.val := by
      have horderedValues : left.val < right.val := hordered
      omega
    rw [d7RootContainingEmbedding_nonroot position left hleftPositive,
      d7RootContainingEmbedding_nonroot position right hrightPositive]
    exact hmatch.trans hbits.2

noncomputable def d7RootContainingBlockerWitness
    (coloring : Nat → Bool)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (position : Fin 2396) :
    RootContainingBlockerWitness coloring
      (d7SelectedCoreClause (d7RootContainingCorePosition position)) :=
  { embedding := d7RootContainingEmbedding position
    cube := d7RootContainingFullCube position
    representative := (d7RootContainingRepresentative position).cube
    inner := (d7RootContainingRepresentative position).inner
    motif := (d7RootContainingRepresentative position).motif
    motif_mem := (d7RootContainingRepresentative position).motif_mem
    embedding_injective := d7RootContainingEmbedding_injective position
    orbit := d7RootContainingFullCube_orbit position
    representative_forces := (d7RootContainingRepresentative position).forces
    projected_false_gives_full_match :=
      d7RootContainingProjected_false_gives_full_match coloring
        hrootPositive hrootRight position }

/-! ## Selected-core evaluation and branch contradiction -/

theorem d7SelectedCoreClause_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (hunit : ∀ position : Fin 16,
      CNF.Clause.eval coloring
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true)
    (position : Fin 5807) :
    CNF.Clause.eval coloring (d7SelectedCoreClause position) = true := by
  by_cases hbase : position.val < 168
  · let basePosition : Fin 168 := ⟨position.val, hbase⟩
    have hposition : d7BaseCorePosition basePosition = position := by
      apply Fin.ext
      simp [d7BaseCorePosition, basePosition]
    rw [← hposition, d7SelectedBaseClause_eq]
    exact d7BaseClause_eval_true coloring hfree hrootPositive hrootRight
      _ (d7BaseCoreSourceIndex_range basePosition)
  · by_cases hrootFree : position.val < 3395
    · let payloadPosition : Fin 3227 :=
        ⟨position.val - 168, by omega⟩
      have hposition : d7RootFreeCorePosition payloadPosition = position := by
        apply Fin.ext
        simp [d7RootFreeCorePosition, payloadPosition]
        omega
      rw [← hposition]
      exact rootFreeBlockerWitness_eval_true hfree havoid
        (d7RootFreeBlockerWitness payloadPosition)
    · by_cases hrootContaining : position.val < 5791
      · let payloadPosition : Fin 2396 :=
          ⟨position.val - 3395, by omega⟩
        have hposition :
            d7RootContainingCorePosition payloadPosition = position := by
          apply Fin.ext
          simp [d7RootContainingCorePosition, payloadPosition]
          omega
        rw [← hposition]
        exact rootContainingBlockerWitness_eval_true hfree havoid
          (d7RootContainingBlockerWitness coloring hrootPositive hrootRight
            payloadPosition)
      · let unitPosition : Fin 16 := ⟨position.val - 5791, by omega⟩
        have hposition : d7UnitCorePosition unitPosition = position := by
          apply Fin.ext
          simp [d7UnitCorePosition, unitPosition]
          omega
        rw [← hposition]
        exact hunit unitPosition

theorem d7CoreSelection_eval_true
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (havoid : AvoidsCover6 coloring)
    (hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 coloring 0 vertex = true)
    (hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 coloring 0 vertex = false)
    (hunit : ∀ position : Fin 16,
      CNF.Clause.eval coloring
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true) :
    CNF.eval coloring
      ((branchSource fgraveGowCatalogueIndex).selectCNF
        fgraveGowCoreFinIndices) = true := by
  rw [CNF.eval, Array.all_eq_true]
  intro index hindex
  have hsize :
      ((branchSource fgraveGowCatalogueIndex).selectCNF
        fgraveGowCoreFinIndices).clauses.size = 5807 := by
    unfold LRATCatcher.Tests.R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF
    simpa using fgraveGowCoreFinIndexCount
  let position : Fin 5807 := ⟨index, by omega⟩
  have hsatisfied := d7SelectedCoreClause_eval_true coloring hfree havoid
    hrootPositive hrootRight hunit position
  simpa [LRATCatcher.Tests.R44Cover6Master8CoreBridge.IndexedCNFSource.selectCNF,
    d7SelectedCoreClause, d7CoreSourceIndex, d7CoreArrayPosition, position]
    using hsatisfied

theorem no_degreeSeven_fgraveGow_cover6_avoiding
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 12 4 4 coloring)
    (hdegree :
      LRATCatcher.Tests.R44OrderTwelveTwoCenterCases.positiveRootDegree
        coloring = 7)
    (havoid : AvoidsCover6 coloring)
    (sourceToRepresentative : FinPermutation 7)
    (hmap : D7R34FixedIsoData coloring fgraveGowCatalogueIndex
      sourceToRepresentative) : False := by
  let normalized :=
    d7R34RelabeledColoring coloring sourceToRepresentative
  have hnormalizedFree : isRamseyFree 12 4 4 normalized :=
    (d7R34Relabeled_isRamseyFree_iff coloring sourceToRepresentative).mp hfree
  have hnormalizedAvoid : AvoidsCover6 normalized :=
    (d7R34Relabeled_avoidsCover6_iff coloring sourceToRepresentative).mp havoid
  have hrootPositive : ∀ vertex, 1 ≤ vertex → vertex < 8 →
      coloringEdge 12 normalized 0 vertex = true := by
    intro vertex hlower hupper
    let localIndex : Fin 7 := ⟨vertex - 1, by omega⟩
    have hroot := d7R34Relabeled_root_positive coloring hdegree
      sourceToRepresentative localIndex
    have hlabel : (d7PositiveLabel localIndex).val = vertex := by
      simp [d7PositiveLabel, localIndex]
      omega
    simpa [normalized, hlabel] using hroot
  have hrootRight : ∀ vertex, 8 ≤ vertex → vertex < 12 →
      coloringEdge 12 normalized 0 vertex = false := by
    intro vertex hlower hupper
    let localIndex : Fin 4 := ⟨vertex - 8, by omega⟩
    have hroot := d7R34Relabeled_root_right coloring hdegree
      sourceToRepresentative localIndex
    have hlabel : (d7RightLabel localIndex).val = vertex := by
      simp [d7RightLabel, localIndex]
      omega
    simpa [normalized, hlabel] using hroot
  have hunit : ∀ position : Fin 16,
      CNF.Clause.eval normalized
        (d7SelectedCoreClause (d7UnitCorePosition position)) = true := by
    intro position
    rw [d7SelectedUnitClause_eq]
    exact fgraveGowRelabeled_unitTail_eval_true coloring
      sourceToRepresentative hmap (d7SelectedUnitTailPosition position)
  have htrue := d7CoreSelection_eval_true normalized hnormalizedFree
    hnormalizedAvoid hrootPositive hrootRight hunit
  have hfalse := fgraveGowCoreSelection_unsat normalized
  exact Bool.noConfusion (htrue.symm.trans hfalse)

#print axioms d7CorePayloadFiniteChecks
#print axioms d7BaseClause_eval_true
#print axioms d7CoreSelection_eval_true
#print axioms no_degreeSeven_fgraveGow_cover6_avoiding

end LRATCatcher.Tests.R44Cover6Master7R34FgraveGowSemantics
