module DoublesTensor

import Tensor
import Dimension

%access public export
%default total

--------------------------------------------------------------------------------
-- Building
--------------------------------------------------------------------------------

zeros : (dims : Dims n) -> Tensor dims Double
zeros xs = Tensor.fill 0.0 xs

zerosLike : Tensor dims Double -> Tensor dims Double
zerosLike xs = zeros $ get_dims xs

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- There is no preexisting max double.
min : Tensor dims Double -> Double
min xs = Tensor.min 999999999.0 xs

-- Same with min double.
max : Tensor dims Double -> Double
max xs = Tensor.max (999999999.0 * (-1)) xs