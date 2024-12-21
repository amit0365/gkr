Implementing Accumulation friendly GKR from Proofs for Deep Thought https://eprint.iacr.org/2024/325
This work is supported by ZK Grants Round https://blog.ethereum.org/2024/06/25/zk-grants-round-announce
The GKR and sumcheck framework are inspired by the Gnark multilinear GKR and sumcheck implementation. However, we implement an accumulation friendly, a bivariate sumcheck for the GKR. The sumcheck implementation is generic and can be used with more variables.
The util folder including transcript and arithmetic is taken from Han's Plonkish implementation https://github.com/han0110/plonkish.