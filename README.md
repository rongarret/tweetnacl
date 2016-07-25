# Ron's TweetNaCl repo

This is a fork of [TweetNaCl](https://tweetnacl.cr.yp.to) (pronounced "Tweet Salt")  crypto library with the following modifications:

1.  The code has been reformatted using [clang-format](http://clang.llvm.org/docs/ClangFormat.html)

2.  crypto-hash has been refactored to enable the hashing of streamed input

3.  Added code to convert Ed25519 keys to Curve25519 keys to support
[SC4](https://github.com/Spark-Innovations/SC4)

4.  Added some in-line comments based on Appendix D of the [TweetNacl paper](https://tweetnacl.cr.yp.to/tweetnacl-20140917.pdf)
