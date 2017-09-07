function [ f ] = plot_path2d( pt_arr, is_visible )
%PLOT_PATH Summary of this function goes here
%   Detailed explanation goes here

if nargin > 1 && ~is_visible
    f = figure('visible', 'off');
else
    f = figure;
end
plot(pt_arr(end,2), pt_arr(end, 1), 'x', 'color', 'r');
hold on;
plot(pt_arr(1, 2), pt_arr(1, 1), 'o', 'color', 'r');
hold on;
for i = 1:size(pt_arr, 1)
    plot(pt_arr(i, 2), pt_arr(i, 1), '.', 'color', 'b');
    hold on;
end
plot(pt_arr(:,2), pt_arr(:,1), 'color', 'b');

end

