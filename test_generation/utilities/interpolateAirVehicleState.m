function [ X ] = interpolateAirVehicleState( X, indices )
%INTERPOLATEAIRVEHICLESTATE Summary of this function goes here
%   Detailed explanation goes here

for i = indices
    zeroLocs = find(X(:, i) == 0.0);
    for z_i = zeroLocs(1:end)
        k = find(X(1:z_i, i),1,'last');
        if isempty(k)
            k = find(X(z_i:end, i),1,'first');
        end
        if ~isempty(k)
            X(z_i, i) = X(k, i);
        end
    end
end

end

