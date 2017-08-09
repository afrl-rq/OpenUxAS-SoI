function [xdot] = cooptrack(t,x,L,G,c,x0)
%function [xdot] = cooptrack(t,x,L,G,c,x0)
% given the Laplacian Matrix L,
% the pinning Gain Matrix G,
% the gain c and the leader state x0
% Define the Closed Loop System Dynamics for
% the Cooperative Tracking (Pinning Control)
%
% Summer of Innovation, Hybrid Systems Group
%  Wright Brothers Institute
%  Air Force Research Laboratory
%  Lockheed Martin Aeronautics
%  Chris Elliott, July 2017

% note this is for special case xodot = 0 (follow constant value of leader)

% if t>750
%     x0 = 0;
% end

x0bar = ones(length(x),1)*x0;

xdot = -c*(L+G)*(x-x0bar);

end