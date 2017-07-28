function [L, D] = lapl(A)
%function [L, D] = lapl(A)
% given Adjacency Matrix A
% compute the Laplacian Matrix L
% and the Diagonal In-Degree Matrix D
%
% Summer of Innovation, Hybrid Systems Group
%  Wright Brothers Institute
%  Air Force Research Laboratory
%  Lockheed Martin Aeronautics
%  Chris Elliott, July 2017

n = length(A);
L = zeros(n);
D = zeros(n);

for ii = 1:n
    D(ii,ii) = sum(A(ii,:));
end

L = D - A;

if sum(L')*ones(n,1) ~= 0
    error('Invalid Laplacian')
end

end

